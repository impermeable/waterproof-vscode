import { Completion, CompletionContext, CompletionResult, CompletionSource, autocompletion, snippet } from "@codemirror/autocomplete";
import { indentWithTab } from "@codemirror/commands";
import { defaultHighlightStyle, syntaxHighlighting } from "@codemirror/language";
import { coq, coqSyntaxHighlighting } from "./lang-pack"
import { Compartment, EditorState, Extension } from "@codemirror/state"
import {
	EditorView as CodeMirror, keymap as cmKeymap,
	highlightActiveLine,
	lineNumbers, placeholder} from "@codemirror/view"
import { Node, Schema } from "prosemirror-model"
import { EditorView } from "prosemirror-view"
import { customTheme } from "./color-scheme"
import { symbolCompletionSource, coqCompletionSource, tacticCompletionSource, renderIcon } from "../autocomplete";
import { EmbeddedCodeMirrorEditor } from "../embedded-codemirror";
import { linter, LintSource, Diagnostic } from "@codemirror/lint";
import { Debouncer } from "./debouncer";
import { INPUT_AREA_PLUGIN_KEY } from "../inputArea";

/**
 * Export CodeBlockView class that implements the custom codeblock nodeview.
 * Corresponds with the example as can be found here:
 * https://prosemirror.net/examples/codemirror/
 */

export class CodeBlockView extends EmbeddedCodeMirrorEditor {
	dom: HTMLElement;

	private _lineNumberCompartment: Compartment;
	private _lineNumbersExtension: Extension;
	private _dynamicCompletions: Completion[] = [];
	private _readOnlyCompartment: Compartment;
	private _diags;

	private debouncer: Debouncer;

	// Compartment storing the linting information (needs to be in a comp. because of refreshing)
	private _lintingCompartment: Compartment;

	constructor(
		node: Node,
		view: EditorView,
		getPos: (() => number | undefined),
		schema: Schema
	) {
		super(node, view, getPos, schema);
		this._node = node;
		this._outerView = view;
		this._getPos = getPos;
		this._lineNumbersExtension = [];
		this._lineNumberCompartment = new Compartment;
		this._readOnlyCompartment = new Compartment;
		this._lintingCompartment = new Compartment;
		this._diags = [];
		
		// Shadow this._outerView for use in the next function.
		const outerView = this._outerView;

		this._codemirror = new CodeMirror({
			doc: this._node.textContent,
			extensions: [
				// Create the first linting compartment. 
				this._lintingCompartment.of(linter(this.lintingFunction)),
				this._readOnlyCompartment.of(EditorState.readOnly.of(!this._outerView.editable)),
				this._lineNumberCompartment.of(this._lineNumbersExtension),
				autocompletion({
					override: [
						tacticCompletionSource, 
						this.dynamicCompletionSource, 
						symbolCompletionSource, 
						coqCompletionSource
					], 
					icons: false,
					addToOptions: [renderIcon]
				}),
				cmKeymap.of([
					indentWithTab,
					...this.embeddedCodeMirrorKeymap()
				]),
				customTheme,
				syntaxHighlighting(defaultHighlightStyle),
				coq(),
                highlightActiveLine(),
				coqSyntaxHighlighting(),
				CodeMirror.updateListener.of(update => this.forwardUpdate(update)),
				placeholder("Empty code cell")
			],
			// We override the dispatch field to filter the transactions in the CodeMirror cells.
			// We explicitly **allow** selection changes, so that students can select (and copy) non-input area code.
			dispatch(tr, view) {
				// TODO: deprecated according to reference manual? https://codemirror.net/docs/ref/#view.EditorViewConfig.dispatch 

				if (!tr.docChanged && tr.selection) {
					// In the case that the document was not changed **and** that we have a selection update
					// we allow the transaction to update the state.
					view.update([tr]);
				} else {
					// Figure out whether we are in teacher or student mode.
					// This is a ProseMirror object, hence we need the prosemirror view (outerview) state.
					const locked = INPUT_AREA_PLUGIN_KEY.getState(outerView.state)?.locked;
					if (locked === undefined) {
						// if we could not get the locked state then we do not
						// allow this transaction to update the view.
						return;
					}
					
					if (locked) {
						// in student mode.
						const pos = getPos();
						if (pos === undefined) return;
						// Resolve the position in the prosemirror document and get the node one level underneath the root.
						// TODO: Assumption that `<input-area>`s only ever appear one level beneath the root node.
						// TODO: Hardcoded node names.
						const name = outerView.state.doc.resolve(pos).node(1).type.name;
						if (name !== "input") return; // This node is not part of an input area.
					}

					view.update([tr]);
				}
			},
		});

		this.debouncer = new Debouncer(400, this.forceUpdateLinting.bind(this));

		// Editors outer node is dom
		this.dom = this._codemirror.dom;

		// Fix the coqblock not being selectable when editing the markdown blocks.
		this.dom.addEventListener("click", () => {
			this._codemirror.focus();
			this.setEditPermission();
		});

		this.updating = false;
		this.handleNewComplete([]);
	}

	public handleSnippet(template: string, posFrom: number, posTo: number) {
		this._codemirror.focus();
		snippet(template)({
			state: this._codemirror.state,
			dispatch: this._codemirror.dispatch
		}, null, posFrom, posTo);
	}

	private lintingFunction: LintSource = (view: CodeMirror): readonly Diagnostic[] => {
		return this._diags;
	}

	/**
	 * set edit permission
	 */
	setEditPermission(): void {
		// update
		this._codemirror.dispatch({
			effects: this._readOnlyCompartment.reconfigure(
				EditorState.readOnly.of(!this._outerView.editable)
			)
		});
	}

	/**
	 * Update the line numbers extension
	 */
	updateLineNumbers(firstLineNo: number, toggleState: boolean): void {
		this._lineNumbersExtension = lineNumbers({
			formatNumber: (lineNo: number) => (lineNo + firstLineNo - 1).toString()
		});
		this._codemirror.dispatch({
			effects: this._lineNumberCompartment.reconfigure(
				toggleState ? this._lineNumbersExtension : []
			)
		});
	}

	/**
	 * This method needs to be called with the new list to update it.
	 */
	handleNewComplete(newCompletions: Completion[]): void {
		this._dynamicCompletions = newCompletions;
	}

	/**
	 * (Dynamic) Completion Source.
	 * Contains completions for defined theorems/lemmas/etc.
	 */
	dynamicCompletionSource: CompletionSource = (context: CompletionContext): Promise<CompletionResult | null> => {
		return new Promise((resolve, reject) => {
			let before = context.matchBefore(/\w/);
			// If completion wasn't explicitly started and there
			// is no word before the cursor, don't open completions.
			if (!context.explicit && !before) resolve(null);
			resolve({
				from: before ? before.from : context.pos,
				options: this._dynamicCompletions,
				validFor: /[^ ]*/
			});
		});
	};

	/**
	 * Add a new coq error to this view
	 * @param from The from position of the error.
	 * @param to The to postion of the error (should be larger than `from`).
	 * @param message The message attached to this error.
	 * @param severity The severity attached to this error.
	 */
	public addCoqError(from: number, to: number, message: string, severity: number) {
		this._diags.push({
			from, to, 
			message, 
			severity: severityToString(severity),
			actions: [{
				name: "Copy 📋", 
				apply(view: EditorView, from: number, to: number) {
					navigator.clipboard.writeText(message);
				}
			}]
		});
		this.debouncer.call();		
	}

	/**
	 * Helper function that forces the linter function to run. 
	 * Should be called after an error has been added or after the errors have been cleared.
	 */
	private forceUpdateLinting() {
		// Reconfigure the linting compartment (forces the linter to run again when editor idle)
		this._codemirror.dispatch({
			effects: this._lintingCompartment.reconfigure(linter(() => this._diags, {delay: 250}))
		})
	}

	/**
	 * Clear all coq errors from this view.
	 */
	public clearCoqErrors() {
		this._diags = [];
		this.debouncer.call();
	}
}

const severityToString = (sv: number) => {
	switch (sv) {
		case 0: 
			return "error";
		case 1: 
			return "warning";
		case 2: 
			return "info";
		case 3: 
			return "hint";
		default: 
			return "error";
	}
}
