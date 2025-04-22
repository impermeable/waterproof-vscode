import { NodeType, Node as PNode, Schema } from "prosemirror-model";
import { EditorState, EditorStateConfig, Plugin, Transaction } from "prosemirror-state";
import { Decoration, DecorationSet, EditorView } from "prosemirror-view";
import { findDescendantsWithType } from "../utilities";

/**
 * Function that returns the hint plugin.
 * @param schema The schema in use for the editor.
 * @returns A `Plugin` that enables the hint functionality.
 */
export const createHintPlugin = (schema: Schema): Plugin => {
	// Get the hint node type from the supplied schema
    const hintNodeType = schema.nodes.hint;

	// Create a new Plugin
    const plugin = new Plugin<DecorationSet>({
        state: {
            init(config: EditorStateConfig, instance: EditorState) {
				// On the init we recompute all the hint decorations.
                return getHintDecorations(instance, hintNodeType);
            },
            apply(tr: Transaction,
                value: DecorationSet,
                oldState: EditorState,
                newState: EditorState) {
				// If the document did not change (on selection changes for example)
				// we dont have to recompute the hint decorations.
                return tr.docChanged ? getHintDecorations(newState, hintNodeType) : value;
            },
        },
        props: {
            decorations(state: EditorState) {
				// The decorations this plugin provide are stored in the state of the plugin.
                return this.getState(state);
            }
        }
    });
	// Return the plugin object.
    return plugin;
}

/**
 * Compute the set of hint decorations given the state of the editor and the type of a hint node.
 * @param state The state of the editor.
 * @param hintNodeType The type of a hint node as defined in the schema.
 * @returns A `DecorationSet` containing the decorations for the hint nodes.
 */
function getHintDecorations(state: EditorState, hintNodeType: NodeType): DecorationSet {
	// Use the `findDescendantsWithType` helper to get all nodes of type `hintNodeType` in the editor.
	const hints = findDescendantsWithType(state.doc, true, hintNodeType)
		.filter(result => result.node.content.size > 0);

	// Build a decoration array from the found hint nodes.
	const decorations = hints.map((hint) => {
		// Create a new widget decoration for every hint node.
		const widgetDeco = Decoration.widget(hint.pos,
			// Pass a DOM rendering function.
			(view: EditorView) => createCollapseDOM(view, hint),
			// Display this DOM *before* the actual hint content.
			{side: -1});
		return widgetDeco;
	});
	// Create a new DecorationSet from the decorations and the document structure.
	const hintDecorationSet = DecorationSet.create(state.doc, decorations);
	return hintDecorationSet;
}

/**
 *
 * @param view The current editor view.
 * @param hint The `hint` object (as returned by `findDescendantsWithType`)
 * @returns
 */
function createCollapseDOM(view: EditorView, hint: {node: PNode, pos: number}) {
	// Create hint title element.
	const hintElement = document.createElement("div");
	hintElement.classList.add("hint-title-element");
	// Set the content to the title attribute of the hint node.
	hintElement.textContent = hint.node.attrs.title;
	// Add event listener for mouse clicks.
	hintElement.addEventListener("click", (_ev: MouseEvent) => {
		// Get the state of the hint attribute ( assuming it is always there :) ).
		const state = view.state.doc.nodeAt(hint.pos)?.attrs.shown as boolean;
		// Create a new transaction that toggles the 'shown' node attribute on the node at position `hint.pos`.
		const trans = view.state.tr.setNodeAttribute(hint.pos, "shown", !state);
		// Dispatch the transaction.
		view.dispatch(trans);
	});
	return hintElement;
}