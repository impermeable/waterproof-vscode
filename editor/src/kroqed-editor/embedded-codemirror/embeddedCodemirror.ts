import { EditorView as CodeMirror, KeyBinding, ViewUpdate } from "@codemirror/view";
import { Node as PNode, Schema } from "prosemirror-model";
import { TextSelection, Selection, Transaction } from "prosemirror-state";
import { Decoration, DecorationSource, EditorView, NodeView } from "prosemirror-view";
import { MovementDirection, MovementUnit } from "./types";
import { exitCode } from "prosemirror-commands";
import { selectAll } from "@codemirror/commands";
import { keybindings } from "./embedded-codemirror-keymap";

/**
 * A class implementing everything required to create an embedded codemirror editor for prosemirror.
 * Implements the `NodeView` prosemirror class. Can be extended to create custom codemirror editors like
 * the one used to edit markdown or coq.
 */
export class EmbeddedCodeMirrorEditor implements NodeView {
    public _getPos: (() => number | undefined);

    // Whether the inner editor (the codemirror instance) is updating.
	protected updating: boolean;
	// The inner codemirror editor view.
    protected _codemirror: CodeMirror;
	// The outer prosemirror editor view.
    protected _outerView: EditorView;
	// The schema in use for the prosemirror editor.
    protected _schema: Schema;
	// The node for which this editor was created.
    protected _node: PNode;

    constructor(
        node: PNode,
		view: EditorView,
		getPos: (() => number | undefined),
		schema: Schema
    ) {
		// Store parameters.
        this._node = node;
        this._outerView = view;
        this._getPos = getPos;
        this._schema = schema;
    }

    dom: Node;
    contentDOM?: HTMLElement | null | undefined;

    update(node: PNode, decorations: readonly Decoration[], innerDecorations: DecorationSource) {
		// Ignore the update if the type of `node` is not the same as the internal node type.
		if (node.type != this._node.type) return false;

		// Set internal node equal to node.
		this._node = node;

		// If is updating return early
		if (this.updating) return true;

		// Extract node text (the edit) and document (current) text.
		let newText = node.textContent;
		let curText = this._codemirror.state.doc.toString();

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
			this.updating = true;
			// Update the codemirror instance from 'start' to 'curEnd' with the corresponding slice of the newText.
			this._codemirror.dispatch({
				changes: {
					from: start,
					to: curEnd,
					insert: newText.slice(start, newEnd)
				}
			});
			// Set updating to false again.
			this.updating = false;

		}
		return true;
	}

    selectNode?: (() => void) | undefined;
    deselectNode?: (() => void) | undefined;
    
    setSelection(anchor: number, head: number, root: Document | ShadowRoot) {
		// Focus on the internal codemirror instance.
		// TODO: Is this the culprit of the selectParent bug?
		// this._codemirror.focus(); 
		// Set updating state to true while updating selection.
		this.updating = true;
		// Update the selection within the codemirror instance.
		this._codemirror.dispatch({ selection: { anchor, head } });
		// Reset updating state to false.
		this.updating = false;
	}

    stopEvent?: ((event: Event) => boolean) | undefined;
    ignoreMutation?: ((mutation: MutationRecord) => boolean) | undefined;
    destroy?(): void;

	forwardUpdate(update: ViewUpdate): void {
		// Get the current cursor position.
		let pos = this._getPos();
		// If there is no position we are done.
		if (!pos) return;
		// If we are updating or we don't have focus then we should return early.
		if (this.updating || !this._codemirror.hasFocus) return;

		// Figure out offset position from selection.
		let offset = pos + 1, { main } = update.state.selection;
		// Get selection from and to.
		let selFrom = offset + main.from, selTo = offset + main.to;
		// Get the selection from the outer view.
		let pmSel = this._outerView.state.selection;
		// If either the document changed or the selections do not match...
		if (update.docChanged || pmSel.from != selFrom || pmSel.to != selTo) {
			//..then we get the currnt transaction
			let tr = this._outerView.state.tr;
			update.changes.iterChanges((fromA, toA, fromB, toB, text) => {
				//..iterate over all changes and create text changes in the outer editor.
				if (text.length) {
					tr.replaceWith(offset + fromA, offset + toA,
						this._schema.text(text.toString()));
				}
				else {
					tr.delete(offset + fromA, offset + toA);
					offset += (toB - fromB) - (toA - fromA);
				}
			});
		  	tr.setSelection(TextSelection.create(tr.doc, selFrom, selTo));
		  	this._outerView.dispatch(tr);
		}
	}
    

    /**
	 * Do a movement, but first check if we escape the current view.
	 * @param unit The movement unit (could be a line (up and down) or a character (left to right))
	 * @param dir The direction either forward or backward.
	 * @returns
	 */
	maybeEscape(unit: MovementUnit, dir: MovementDirection): boolean {
		// Get the current position.
		let pos = this._getPos();
		// If there is none, we can't escape this view,
		if (!pos) return false;

		// Get the current state and the main selection related to this state.
		let _state = this._codemirror.state;
		let _mainSelection = _state.selection.main;

		// If there is no main selection this is a no-op.
		if (!_mainSelection.empty) return false;

		let targetPos: number;
		let selection: Selection;

		switch (unit) {
			case MovementUnit.line:
				let $_mainSelection = _state.doc.lineAt(_mainSelection.head);
				if (dir == MovementDirection.backward) {
					if ($_mainSelection.from > 0) {
						// There is room in this view to move backwards.
						return false;
					}
				} else {
					if ($_mainSelection.to < _state.doc.length) {
						// There is still room to move forward.
						// We are not at the end of the document.
						return false;
					}
				}
				targetPos = pos + (dir < 0 ? 0 : this._node.nodeSize);
				selection = Selection.near(this._outerView.state.doc.resolve(targetPos), dir);
				break;
			case MovementUnit.character:
				if (dir == MovementDirection.backward ? _mainSelection.from > 0 : _mainSelection.to < _state.doc.length) return false;
				targetPos = pos + (dir < 0 ? 0 : this._node.nodeSize);
				selection = Selection.near(this._outerView.state.doc.resolve(targetPos), dir);
				break;
			default:
				return false;
		}

		// Create new selection transaction...
		let transaction: Transaction = this._outerView.state.tr.setSelection(selection).scrollIntoView();
		// dispatch it..
		this._outerView.dispatch(transaction);
		// and focus on the outer editor.
		this._outerView.focus();
		return true;
	}

    // Setup codemirror keymap
	embeddedCodeMirrorKeymap(): KeyBinding[] {
		let view = this._outerView;

		// 'Mod' is a platform independent 'Ctrl'/'Cmd'
		return [
			...keybindings,
			{ key: "ArrowUp", run: () => this.maybeEscape(MovementUnit.line, MovementDirection.backward) },
			{ key: "ArrowLeft", run: () => this.maybeEscape(MovementUnit.character, MovementDirection.backward) },
			{ key: "ArrowDown", run: () => this.maybeEscape(MovementUnit.line, MovementDirection.forward) },
			{ key: "ArrowRight", run: () => this.maybeEscape(MovementUnit.character, MovementDirection.forward) },
			{
				key: "Mod-Enter", run: () => {
					if (!exitCode(view.state, view.dispatch)) return false
					view.focus()
					return true
				}
			},
			{ key: "Mod-A", run: selectAll }
		]
	}
}