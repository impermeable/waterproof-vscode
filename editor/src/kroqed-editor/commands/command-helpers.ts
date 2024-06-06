/////// Helper functions /////////

import { NodeType, Node as PNode } from "prosemirror-model";
import { EditorState, TextSelection, Transaction, Selection, NodeSelection } from "prosemirror-state";
import { INPUT_AREA_PLUGIN_KEY } from "../inputArea";

/////// Helper functions /////////

/**
 * Get a selection type object from a user selection.
 * @param sel Input user selection.
 * @returns Object that stores booleans whether we have a text or node selection.
 */
export function selectionType(sel: Selection) {
    return {
        isTextSelection: sel instanceof TextSelection,
        isNodeSelection: sel instanceof NodeSelection
    }
}

/**
 * Traverse up the tree (decreasing depth) and return the first node with a given name. 
 * @param state The current editor state.
 * @param name The name of the node we are interested in.
 * @returns The start and end position of the node with name `name`.
 */
export function traverseUpAndReturnFirstWithName(state: EditorState, name: string) {
    const sel= state.selection;
    const depth = sel.$from.depth;
    let foundDepth = 0;
    for (let i = depth; i >= 0; i--) {
        if (sel.$from.node(i).type.name === name) {
            foundDepth = i;
            break;
        }
    }
    const node = sel.$from.node(foundDepth);
    const start = sel.$from.posAtIndex(0, foundDepth) - 1;
    const end = start + node.nodeSize;
    return { start, end };
}

/**
 * Helper function for inserting a new node above the currently selected one.
 * @param state The current editor state.
 * @param tr The current transaction for the state of the editor. 
 * @param escapeContainingNode Whether to escape the containing node. 
 * @param nodeType Array of nodes to insert. Depending on the node type this will be either one or more 
 * (coqcode outside of a coqblock needs to be enclosed within a new coqblock)
 * @returns An insertion transaction.
 */
export function insertAbove(state: EditorState, tr: Transaction, ...nodeType: NodeType[]): Transaction {
    const sel = state.selection;
    const {isTextSelection, isNodeSelection} = selectionType(sel);
    let trans: Transaction = tr;

    if (isNodeSelection) {
        // To and from point directly to beginning and end of node.
        const pos = sel.from;
        let counter = pos;
        nodeType.forEach(type => {
            trans = trans.insert(counter, type.create());
            counter++;
        });
    } else if (isTextSelection) {
        const textSel = (sel as TextSelection);
        const from = sel.from - textSel.$from.parentOffset;
        let counter = from;
        nodeType.forEach(type => {
            trans = trans.insert(counter, type.create());
            counter++;
        });
    }

    return trans;
}

/**
 * Helper function for inserting a new node underneath the currently selected one.
 * @param state The current editor state.
 * @param tr The current transaction for the state of the editor. 
 * @param escapeContainingNode Whether to escape the containing node. 
 * @param nodeType Array of nodes to insert. Depending on the node type this will be either one or more 
 * (coqcode outside of a coqblock needs to be enclosed within a new coqblock)
 * @returns An insertion transaction.
 */
export function insertUnder(state: EditorState, tr: Transaction, ...nodeType: NodeType[]): Transaction {
    const sel = state.selection;
    const {isTextSelection, isNodeSelection} = selectionType(sel);

    let trans: Transaction = tr;

    if (isNodeSelection) {
        // To and from point directly to beginning and end of node.
        const pos = sel.to;
        let counter = pos;
        nodeType.forEach(type => {
            trans = trans.insert(counter, type.create());
            counter++;
        });
    } else if (isTextSelection) {
        const textSel = (sel as TextSelection);
        const to = sel.to + (sel.$from.parent.nodeSize - textSel.$from.parentOffset) - 1;
        let content: PNode | null = null;

        if (to > state.doc.nodeSize) {
            console.log("This is no bueno");
            return trans;
        }
        let counter = to;
        nodeType.forEach(type => {
            trans = trans.insert(counter, type.create());
            counter++;
        });
    }

    return trans;
}

/**
 * Returns the containing node for the current selection.
 * @param sel The user's selection.
 * @returns The node containing this selection. Will *not* return text nodes.
 */
export function getContainingNode(sel: Selection): PNode | undefined {
    const {isTextSelection, isNodeSelection} = selectionType(sel);

    if (isTextSelection) {
        return sel.$from.node(sel.$from.depth - 1);
    } else if (isNodeSelection) {
        return sel.$from.parent;
    } else {
        return undefined;
    }
}

export function allowedToInsert(state: EditorState): boolean {
    const pluginState = INPUT_AREA_PLUGIN_KEY.getState(state);
    if (!pluginState) return false;
    const isTeacher = !pluginState.locked;
    // If in global locking mode, disallow everything
    if (pluginState.globalLock) return false;
    // If the user is in teacher mode always return `true`, if not
    // we check wether they are in a input area. 
    return isTeacher ? true : checkInputArea(state.selection);
}

/**
 * Helper function for checking if the selection is within an input area.
 * @returns Whether the selection is within an input area. 
 */
export function checkInputArea(sel: Selection): boolean {
    const from = sel.$from;
    const depth = from.depth;
    // An input area can only ever have depth = 1, since it is a 
    // top level node (see TheSchema in `kroqed-schema.ts`)
    if (depth < 1) return false;
    return from.node(1).type.name === "input";
}