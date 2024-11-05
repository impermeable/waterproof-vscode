import { indentWithTab, indentMore, indentLess } from "@codemirror/commands"
import {
	EditorView as CodeMirror, ViewUpdate, keymap as cmKeymap,
	placeholder
} from "@codemirror/view"

import { Node, Schema } from "prosemirror-model"
import { PluginKey, TextSelection } from "prosemirror-state"
import { Decoration, EditorView } from "prosemirror-view"
import { SwitchableView } from "./SwitchableView"
import { editorTheme } from "./EditorTheme"
import { renderIcon, symbolCompletionSource } from "../../autocomplete"
import { autocompletion, acceptCompletion } from "@codemirror/autocomplete"
import { EmbeddedCodeMirrorEditor } from "../../embedded-codemirror"

/**
 * Export CodeBlockView class that implements the custom codeblock nodeview.
 * Corresponds with the example as can be found here:
 * https://prosemirror.net/examples/codemirror/
 */

function customTab(view: CodeMirror){
	if (acceptCompletion(view)) {
        return true; 
    }
	return indentMore(view)

}
export class EditableView extends EmbeddedCodeMirrorEditor {
    public view: CodeMirror;
	private _parent: SwitchableView;
	private _pluginKey: PluginKey;

	constructor (
        node: Node, 
		outerView: EditorView, 
		schema: Schema, 
		getPos: (() => number | undefined), 
		place: HTMLElement, 
		parent: SwitchableView, 
		pluginKey: PluginKey
	) {
		super(node, outerView, getPos, schema);
		this._node = node;
		this._parent = parent;
		this._outerView = outerView;
		this._getPos = getPos;
		this._schema = schema;
		this._pluginKey = pluginKey;
		this.view = new CodeMirror({
			doc: this._node.textContent,
			extensions: [
				cmKeymap.of([{
					key: "Tab",
					run: customTab, 
					shift: indentLess,
					preventDefault: false 
				},
					...this.embeddedCodeMirrorKeymap(),
				]),
				CodeMirror.updateListener.of(update => this.forwardUpdate(update)),
				placeholder("Empty..."),
				autocompletion({
					// In the markdown / coqdoc editing add the symbol and emoji completions.
					override: [symbolCompletionSource],
					icons: false,
					addToOptions: [renderIcon]
				}),
				CodeMirror.lineWrapping,
				editorTheme
			]
		});
		place.appendChild(this.view.dom);
	}

	focus() { this.view.focus(); }
    destroy() { this.view.destroy(); }

	// Overwrites the base method in EmbeddedCodeMirrorEditor.
	forwardUpdate(update: ViewUpdate): void {
		// Get the current cursor position.
		let pos = this._getPos();
		// If there is no position we are done.
		if (pos === undefined) return;
		// If we are updating or we don't have focus then we should return early.
		if (this._parent.updating || !this.view.hasFocus) return;

		// TODO: Comments
		let offset = pos + 1, {main} = update.state.selection;
		let selFrom = offset + main.from, selTo = offset + main.to;
		let pmSel = this._outerView.state.selection;
		if (update.docChanged || pmSel.from != selFrom || pmSel.to != selTo) {
			let tr = this._outerView.state.tr;
			update.changes.iterChanges((fromA, toA, fromB, toB, text) => {
				if (text.length) {
					tr.replaceWith(offset + fromA, offset + toA,
								this._schema.text(text.toString()));
				}
				else {
					tr.delete(offset + fromA, offset + toA);
					offset += (toB - fromB) - (toA - fromA);
				}
			});
			tr.setMeta(this._pluginKey, TextSelection.create(tr.doc,selFrom, selTo));
		  	this._outerView.dispatch(tr);
		}
	}

	// Overwrites the base method in EmbeddedCodeMirrorEditor.
	update(node: Node, decorations: readonly Decoration[]) {

		// If is updating return early
		if (this._parent.updating) return true;

		// Extract node text (the edit) and document (current) text.
		let newText = node.textContent;
		let curText = this.view.state.doc.toString();

		// Check whether they are the same.
		// We don't need to update if they are.
		if (newText != curText) {
			// Set start.
			let start = 0;
			// The current length of the document.
			let curEnd = curText.length;
			// The new length of the document.
			let newEnd = newText.length;

			// Figure out what range of characters needs to be replaced.
			// All matching characters can be safely ignored.
			while (start < curEnd &&
					curText.charCodeAt(start) == newText.charCodeAt(start)) {
				++start;
			}
			while (curEnd > start && newEnd > start &&
					curText.charCodeAt(curEnd - 1) == newText.charCodeAt(newEnd - 1)) {
				curEnd--;
				newEnd--;
			}

			// Set updating to true before dispatching transaction.
			this._parent.updating = true;
			// Update the codemirror instance from 'start' to 'curEnd' with the corresponding slice of the newText.
			this.view.dispatch({
				changes: {
					from: start,
					to: curEnd,
					insert: newText.slice(start, newEnd)
				}
			});
			// Set updating to false again.
			this._parent.updating = false;

		}
		return true;
	}

}