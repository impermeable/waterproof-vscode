import { Completion, CompletionContext, CompletionResult, CompletionSource, autocompletion, snippet, completionKeymap, acceptCompletion } from "@codemirror/autocomplete";
import { defaultHighlightStyle, syntaxHighlighting } from "@codemirror/language";
import { coq, coqSyntaxHighlighting } from "./lang-pack"
import { Compartment, EditorState, Extension, StateCommand, SelectionRange, ChangeSpec, Line, EditorSelection } from "@codemirror/state"
import {
	EditorView as CodeMirror, keymap as cmKeymap,
	highlightActiveLine,
	lineNumbers, placeholder} from "@codemirror/view"
import { Node, Schema } from "prosemirror-model"
import { EditorView } from "prosemirror-view"
import { customTheme } from "./color-scheme"
import { symbolCompletionSource, coqCompletionSource, tacticCompletionSource, renderIcon } from "../autocomplete";
import { EmbeddedCodeMirrorEditor } from "../embedded-codemirror";
import { linter, LintSource, Diagnostic, setDiagnosticsEffect } from "@codemirror/lint";
import { Debouncer } from "./debouncer";
import { INPUT_AREA_PLUGIN_KEY } from "../inputArea";
import { indentUnit } from "@codemirror/language";

/**
 * Export CodeBlockView class that implements the custom codeblock nodeview.
 * Corresponds with the example as can be found here:
 * https://prosemirror.net/examples/codemirror/
 */
function changeBySelectedLineCustom(state: EditorState, f: (line: Line, changes: ChangeSpec[], range: SelectionRange) => void) {
	let atLine = 2
	return state.changeByRange(range => {
	  let changes: ChangeSpec[] = []
	  for (let pos = range.from; pos <= range.to;) {
		let line = state.doc.lineAt(pos)
		if (line.number < atLine && (range.empty || range.to > line.from)) {
		  f(line, changes, range)
		  atLine = line.number
		}
		pos = line.to + 1
	  }
	  let changeSet = state.changes(changes)
	  return {changes,
			  range: EditorSelection.range(changeSet.mapPos(range.anchor, 1), changeSet.mapPos(range.head, 1))}
	})
  }
export const indentMoreCustom: StateCommand = ({state, dispatch}) => {
	if (state.readOnly) return false
	dispatch(state.update(changeBySelectedLineCustom(state, (line, changes) => {
	  changes.push({from: line.from, insert: state.facet(indentUnit)})
	}), {userEvent: "input.indent"}))
	return true
  }
function customTab(view: CodeMirror){	
	if (acceptCompletion(view)) {
        return true; 
    }
	return indentMoreCustom(view)

}
export class CodeBlockView extends EmbeddedCodeMirrorEditor {
	dom: HTMLElement;

	private _lineNumberCompartment: Compartment;
	private _lineNumbersExtension: Extension;
	private _dynamicCompletions: Completion[] = [];
	private _readOnlyCompartment: Compartment;
	private _diags;

	private debouncer: Debouncer;

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
		this._diags = [];
		
		// Shadow this._outerView for use in the next function.
		const outerView = this._outerView;

		this._codemirror = new CodeMirror({
			doc: this._node.textContent,
			extensions: [
				// Add the linting extension for showing diagnostics (errors, warnings, etc) 
				linter(this.lintingFunction),
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
					addToOptions: [renderIcon],
					defaultKeymap: false,
					
					
			
				}),
				cmKeymap.of([
				...completionKeymap,
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
				// TODO: deprecated according to reference manual https://codemirror.net/docs/ref/#view.EditorViewConfig.dispatch 
				if (!tr.docChanged) {
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
		this._codemirror.dispatch({
			effects: setDiagnosticsEffect.of(this._diags)
		});
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
