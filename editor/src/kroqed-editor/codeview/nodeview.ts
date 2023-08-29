import { Completion, CompletionSource, autocompletion } from "@codemirror/autocomplete";
import { defaultKeymap, indentWithTab } from "@codemirror/commands";
import { defaultHighlightStyle, syntaxHighlighting } from "@codemirror/language";
import { coq, coqSyntaxHighlighting } from "./lang-pack"
import { Compartment, EditorState, Extension } from "@codemirror/state"
import {
	EditorView as CodeMirror, keymap as cmKeymap,
	lineNumbers, placeholder
} from "@codemirror/view"
import { Node, Schema } from "prosemirror-model"
import { EditorView } from "prosemirror-view"
import { customTheme } from "./color-scheme"
import { addCoqErrorMark, clearCoqErrorMarks, removeCoqErrorMark } from "./coq-errors";
import { symbolCompletionSource, coqCompletionSource, tacticCompletionSource } from "./autocomplete";
import { EmbeddedCodeMirrorEditor } from "../embedded-codemirror";

/**
 * Export CodeBlockView class that implements the custom codeblock nodeview.
 * Corresponds with the example as can be found here:
 * https://prosemirror.net/examples/codemirror/
 */

export class CodeBlockView extends EmbeddedCodeMirrorEditor {
	dom: HTMLElement;

	// TODO:
	private _lineNumberCompartment: Compartment;
	private _lineNumbersExtension: Extension;
	private _theoremList: Completion[] = [];
	private _autocompletionCompartment: Compartment;
	private _readOnlyCompartment: Compartment;

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
		this._autocompletionCompartment = new Compartment;
		this._readOnlyCompartment = new Compartment;

		this._codemirror = new CodeMirror({
			doc: this._node.textContent,
			extensions: [
				this._readOnlyCompartment.of(EditorState.readOnly.of(!this._outerView.editable)),
				this._lineNumberCompartment.of(this._lineNumbersExtension),
				this._autocompletionCompartment.of(autocompletion()),
				cmKeymap.of([
					indentWithTab,
					...this.embeddedCodeMirrorKeymap(),
					...defaultKeymap,
				]),
				customTheme,
				syntaxHighlighting(defaultHighlightStyle),
				coq(),
				coqSyntaxHighlighting(),
				CodeMirror.updateListener.of(update => this.forwardUpdate(update)),
				placeholder("Empty code cell")
			]
		});

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
		this._theoremList = newCompletions;
		this.updateAutocompletion(this.standardCompletionSource)
	}

	/**
	 * Standard function that is needed for codemirror autocomplete.
	 * Uses `options` for the list of completions.
	 */
	standardCompletionSource: CompletionSource = context => {
		let before = context.matchBefore(/(\w+\-*\'*)+/);
		// If completion wasn't explicitly started and there
		// is no word before the cursor, don't open completions.
		if (!context.explicit && !before) return null;
		return {
			from: before ? before.from : context.pos,
			options: this._theoremList,
			validFor: /^\w*$/
		};
	};

	/**
	 * Updating the autocompletion to include the new theoremList
	 */
	updateAutocompletion(completionFunction: CompletionSource): void {
		this._codemirror.dispatch({
			effects: this._autocompletionCompartment.reconfigure(
				autocompletion({
					// Add autocompletion sources
					override: [completionFunction, coqCompletionSource, symbolCompletionSource, tacticCompletionSource]
				})
			)
		})
	}

	/**
	 * Add a new coq error to this view
	 * @param from The from position of the error.
	 * @param to The to postion of the error (should be larger than `from`).
	 * @param message The message attached to this error.
	 * @param severity The severity attached to this error.
	 */
	public addCoqError(from: number, to: number, message: string, severity: number) {
		addCoqErrorMark(this._codemirror, {from, to}, message, severity);
	}

	/**
	 * Remove a coq error given a position.
	 * @param from The from position of the error.
	 * @param to The to position of the error.
	 */
	public removeCoqError(from: number, to: number) {
		removeCoqErrorMark(this._codemirror, {from, to});
	}

	/**
	 * Clear all coq errors from this view.
	 */
	public clearCoqErrors() {
		clearCoqErrorMarks(this._codemirror);
	}
}