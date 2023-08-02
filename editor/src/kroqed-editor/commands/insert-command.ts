import { Command, EditorState, Transaction } from "prosemirror-state";
import { FileFormat } from "../../../../shared";
import { InsertionFunction, InsertionPlace } from "./types";
import { NodeType } from "prosemirror-model";
import { EditorView } from "prosemirror-view";
import { allowedToInsert, getContainingNode, getNearestPosOutsideCoqblock } from "./command-helpers";

/**
 * Return a Markdown insertion command.
 * @param filef The file format of the file in use.
 * @param insertionFunction The function used to insert the node into the editor.
 * @param place Where to insert the node into the editor. Either Above or Underneath the currently selected node.
 * @param mvNodeType The node to use in the case of a `.mv` file.
 * @param vNodeType The node to use in the case of a `.v` file.
 * @returns The insertion command.
 */
export function getMdInsertCommand(
    filef: FileFormat,
    insertionFunction: InsertionFunction,
    place: InsertionPlace,
    mvNodeType: NodeType,
    vNodeType: NodeType
): Command {
    return (state: EditorState, dispatch?: ((tr: Transaction) => void), view?: EditorView): boolean => {
        // Early return when inserting is not allowed
        if (!allowedToInsert(state)) return false;

        // This command has no expected outcome when the Fileformat is unknown.
        if (filef === FileFormat.Unknown) return false;

        // Retrieve the correct node given the fileformat.
        const nodeType = filef == FileFormat.MarkdownV ? mvNodeType : vNodeType;

        // Get the containing node for this selection.
        const container = getContainingNode(state.selection);

        let trans: Transaction | undefined;
        if (container === undefined) return false;

        // Retrieve the name of the containing node.
        const { name } = container.type;

        if (filef === FileFormat.MarkdownV) {
            if (name === "input" || name === "hint" || name === "doc") {
                // In the case of having `input`, `hint` or `doc` as parent node, we can insert directly
                // above or below the selected node.
                trans = insertionFunction(state, state.tr, nodeType);
            } else if (name === "coqblock" || name === "coqdoc") {
                // In the case that the user has a selection within a coqblock or coqdoc cell we need to do more work and
                // figure out where this block `starts` and `ends`.
                const { start, end } = getNearestPosOutsideCoqblock(state.selection, state);
                trans = state.tr.insert(place == InsertionPlace.Above ? start : end, nodeType.create());
            }

        } else {
            // This command behaves differently in the case of a .v file. 
            // But since .v files are not working atm, this case is defaulted to false.
            return false;
        }

        // If the dispatch is given and transaction is not undefined dispatch it.
        if (dispatch && trans) dispatch(trans);

        // successful command.
        return true;
    }
}

/**
 * Returns an insertion command for insertion display latex into the editor.
 * @param filef The file format of the file currently being edited.
 * @param insertionFunction The insertion function to use.
 * @param place The place to insert into, either Above or Underneath the currently selected node.
 * @param latexNodeType The node type for a 'display latex' node.
 * @returns The insertion command.
 */
export function getLatexInsertCommand(
    filef: FileFormat,
    insertionFunction: InsertionFunction,
    place: InsertionPlace,
    latexNodeType: NodeType,
): Command {
    return (state: EditorState, dispatch?: ((tr: Transaction) => void), view?: EditorView): boolean => {
        // Early return when inserting is not allowed.
        if (!allowedToInsert(state)) return false;
        // Containing node.
        const container = getContainingNode(state.selection);

        let trans: Transaction | undefined;
        if (container === undefined) return false;

        const { name } = container.type

        // FIXME: This command should behave differently in the case of a .v file, since 
        // the math-display should then be part of a coqblock.

        if (name === "input" || name === "hint" || name === "doc") {
            // `Easy` insertion since we can just insert directly above or below the selection.
            trans = insertionFunction(state, state.tr, latexNodeType);
        } else if (name === "coqblock" || name === "coqdoc") {
            // More difficult insertion since we have to `escape` the current coqblock.
            const { start, end } = getNearestPosOutsideCoqblock(state.selection, state);
            trans = state.tr.insert(place == InsertionPlace.Above ? start : end, latexNodeType.create());
        }

        // Dispatch the transaction when dispatch is given and transaction is not undefined.
        if (dispatch && trans) dispatch(trans);

        // Indicate successful command.
        return true;
    }
}

/**
 * Returns an insertion command for inserting a new coq code cell. Will create a new coqblock if necessary.
 * @param filef The file format of the file that is being edited.
 * @param insertionFunction The insertion function to use.
 * @param place The place of insertion, either Above or Underneath the currently selected node.
 * @param coqblockNodeType The node type of a coqblock node (contains coqdoc and coqcode).
 * @param coqcodeNodeType The node type of a coqcode node.
 * @returns The insertion command.
 */
export function getCoqInsertCommand(
    filef: FileFormat, 
    insertionFunction: InsertionFunction,
    place: InsertionPlace,
    coqblockNodeType: NodeType, 
    coqcodeNodeType: NodeType,
): Command {
    return (state: EditorState, dispatch?: ((tr: Transaction) => void), view?: EditorView): boolean => {
        // Again, early return when inserting is not allowed. 
        if (!allowedToInsert(state)) return false;
        // Retrieve the name containing node of the selection.
        const name = getContainingNode(state.selection)?.type.name;
        if (name === undefined) return false;
        let trans: Transaction | undefined;

        // FIXME: The insertion of a coqcell should be dependent on whether we are working with a .mv or .v file.

        if (name === "input" || name === "hint" || name === "doc") {
            // Create a new coqblock *and* coqcode cell and insert Above or Underneath the current selection.
            trans = insertionFunction(state, state.tr, coqblockNodeType, coqcodeNodeType);
        } else if (name === "coqblock" || name === "coqdoc") {
            // Find the position outside of the coqblock and insert a new coqblock and coqcode cell above or underneath.
            const {start, end} = getNearestPosOutsideCoqblock(state.selection, state);
            const pos = place == InsertionPlace.Above ? start : end;
            trans = state.tr.insert(pos, 
                coqblockNodeType.create()).insert(pos + 1,coqcodeNodeType.create());
        }

        // If dispatch is given and transaction is set, dispatch the transaction.
        if (dispatch && trans) dispatch(trans);

        // Indicate that this command was successful.
        return true;
    }
}