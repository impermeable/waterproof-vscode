import { Completion, CompletionContext, CompletionResult, CompletionSource, autocompletion, snippet, completionKeymap } from "@codemirror/autocomplete";
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
import { linter, LintSource, Diagnostic, setDiagnosticsEffect } from "@codemirror/lint";
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

		// Helper function to create the placeholder content for the codemirror cells.
		const placeholderContent = (): HTMLDivElement => {
			const div = document.createElement("div");
			const pos = getPos();
			if (pos === undefined) {
				div.innerText = "Empty code cell";
				return div;
			}
			const name = outerView.state.doc.resolve(pos).node(1).type.name;
			if (name === "input") {
				// This codemirror cell is part of an input area, we change
				// the placeholder to `(* Type your proof here *)` and apply
				// the appropriate styling.
				div.innerText = "(* Type your proof here *)";
				// The styling of this class is
				// defined in `editor/src/kroqed-editor/styles/input-area.css`.
				div.classList.add("empty-proof-placeholder");
			} else {
				// This codemirror cell is not part of an input area, use the
				// `Empty code cell` placeholder.
				div.innerText = "Empty code cell";
			}

			return div;
		}

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
				placeholder(placeholderContent())
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
		const severityString = severityToString(severity);
		const errorsCount = this._diags.filter(diag => diag.from === from && diag.to === to && diag.severity === "error").length;
		//all diags have the copy action
		const actions = [{
			name: "Copy 📋",
			apply: (view: CodeMirror, from: number, to: number) => {
				// give focus to this current codeblock instante to ensure it updates
				this._codemirror.focus();
				navigator.clipboard.writeText(message);
				this.showCopyNotification(from);
			}
		}];

		if (severityString !== "error") {
			if (errorsCount > 0) {
				actions.push({
					name: "Replace",
					apply:(view: CodeMirror, from: number, to: number) => {
						// give focus to this current codeblock instante to ensure it updates
						this._codemirror.focus();
						const textAtErrorLine = view.state.doc.lineAt(from).text;
						const idents = textAtErrorLine.match(/^(\s*)/g)?.[0] ?? "";
						const trimmedMessage = message.trim();
						const toInsert = idents + trimmedMessage;
						view.dispatch({
							changes: {
								from:from,
								to:to,
								insert: toInsert
							},
						});
						selection: { anchor: from + toInsert.length };
						this.forceUpdateLinting();
					}
				});
			} else {
				actions.push({
					name: "Insert ↓",
					apply:(view: CodeMirror, from: number, to: number) => {
						// give focus to this current codeblock instante to ensure it updates
						this._codemirror.focus();
						const textAtErrorLine = view.state.doc.lineAt(from).text;
						const idents = textAtErrorLine.match(/^(\s*)/g)?.[0] ?? "";
						const trimmedMessage = message.trim();
						const toInsert = "\n".concat(idents, trimmedMessage);
						view.dispatch({
							changes: {
								from: to, to,
								insert: toInsert
							},
							selection: {anchor: to + toInsert.length}
						});
					}
				});
			}
		}

		this._diags.push({
			from:from,
			to:to,
			message: message,
			severity: severityString,
			actions,
		});
		//only when the first error is added, the other diagnostics are updated accordingly
		if (severityString === "error" && errorsCount===0) {
			this.updateDiagnostics(from, to, message);
		}

	}

	private updateDiagnostics(from:number, to:number, message:string) {
		const diagUnchanged = this._diags.filter(diag => diag.from !== from || diag.to !== to);
		const diagnosticsToUpdate = this._diags.filter(diag => diag.from === from && diag.to === to);
		this.clearCoqErrors();
		this._diags = diagUnchanged;
		for (const diag of diagnosticsToUpdate) {
			const actions = [{
				name: "Copy 📋",
				apply: (view: CodeMirror, from: number, to: number) => {
					// give focus to this current codeblock instante to ensure it updates
					this._codemirror.focus();
					navigator.clipboard.writeText(diag.message);
					this.showCopyNotification(from);
				}
			}];
			
			if (diag.severity !== "error"){
				actions.push({
					name: "Replace",
					apply:(view: CodeMirror, from: number, to: number) => {
						// give focus to this current codeblock instante to ensure it updates
						this._codemirror.focus();
						const textAtErrorLine = view.state.doc.lineAt(from).text;
						const idents = textAtErrorLine.match(/^(\s*)/g)?.[0] ?? "";
						const trimmedMessage = diag.message.trim();
						const toInsert = idents + trimmedMessage;
						view.dispatch({
							changes: {
								from:from,
								to:to,
								insert: toInsert
							},
						});
						selection: { anchor: from + toInsert.length };
						this.forceUpdateLinting();
					}
				});
			}

			this._diags.push({
				from: diag.from,
				to: diag.to,
				message: diag.message,
				severity: diag.severity,
				actions
			});
		}
		// Trigger the linter update to refresh diagnostics display
		this.debouncer.call();
	}

	private showCopyNotification(from:number) {
		//coordinates of the the line with the diagnostic
		const coords = this._codemirror.coordsAtPos(from);
	
		if (!coords) {
			console.warn("Could not determine coordinates for diagnostic line.");
			return;
		}
	
		// Create the notification element
		const notification = document.createElement("div");
		notification.textContent = `Copied!`;
		notification.style.position = "fixed";
		notification.style.top = `${coords.bottom + 5}px`; // Position 5px below the line
		notification.style.left = `${coords.left}px`; // Align with the left edge of the line
		notification.style.backgroundColor = "var(--vscode-notifications-background)";
		notification.style.color = "var(--vscode-notifications-foreground)";
		notification.style.padding = "8px";
		notification.style.borderRadius = "5px";
		notification.style.boxShadow = "0 2px 5px rgba(0, 0, 0, 0.3)";
		notification.style.opacity = "1";
		notification.style.transition = "opacity 0.5s ease";
		notification.style.zIndex = "1000"; // Ensure it appears above the editor
	
		document.body.appendChild(notification);
	
		// Fade out after 1 second
		setTimeout(() => {
			notification.style.opacity = "0";
			// Remove the notification from the DOM after the transition
			setTimeout(() => notification.remove(), 500);
		}, 1000);
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
