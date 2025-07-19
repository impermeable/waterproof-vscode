import { NodeType } from "prosemirror-model";
import { EditorState, Transaction } from "prosemirror-state";

/**
 * Enum for the insertion place, can be either `Above` or `Underneath` the currently selected cell.
 */
export enum InsertionPlace {
    Above, 
    Underneath,
}

/**
 * Insertion function type. This type of function is passed to the `get...Command` functions. The function will insert
 * the correct NodeType either above or below the selected node.
 */
export type InsertionFunction = (state: EditorState, trans: Transaction, ...nodeType: NodeType[]) => Transaction;