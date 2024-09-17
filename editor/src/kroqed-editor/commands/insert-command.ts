import { Command, EditorState, Transaction } from "prosemirror-state";
import { FileFormat } from "../../../../shared";
import { InsertionFunction, InsertionPlace } from "./types";
import { NodeType } from "prosemirror-model";
import { EditorView } from "prosemirror-view";
import { allowedToInsert, getContainingNode, traverseUpAndReturnFirstWithName } from "./command-helpers";

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
        // Early return when file format is unknown
        if (filef === FileFormat.Unknown) return false;

        // Early return when inserting is not allowed
        if (!allowedToInsert(state)) return false;

        // Retrieve the correct node given the fileformat.
        const nodeType = filef == FileFormat.MarkdownV ? mvNodeType : vNodeType;

        // Get the containing node for this selection.
        const container = getContainingNode(state.selection);

        let trans: Transaction | undefined;
        if (container === undefined) return false;

        // Retrieve the name of the containing node.
        const { name } = container.type;

        if (name === "input" || name === "hint" || name === "doc") {
            // The following line prevents the insertion of markdown blocks in a .mv file when the cursor 
            //   is inside of an existing markdown block. The insertion action here is ambiguous and the   
            //   default behaviour is confusing, hence this type of insertion is disabled.
            if (filef === FileFormat.MarkdownV) return false;

            // In the case of having `input`, `hint` or `doc` as parent node, we can insert directly
            // above or below the selected node.
            trans = insertionFunction(state, state.tr, nodeType);
        } else if (name === "coqblock" || name === "coqdoc") {
            // In the case that the user has a selection within a coqblock or coqdoc cell we need to do more work and
            // figure out where this block `starts` and `ends`.
            const { start, end } = traverseUpAndReturnFirstWithName(state, "coqblock");
            trans = state.tr.insert(place == InsertionPlace.Above ? start : end, nodeType.create());
        }
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
        // Early return when file format is unknown.
        if (filef === FileFormat.Unknown) return false;
        
        // Early return when inserting is not allowed.
        if (!allowedToInsert(state)) return false;

        // Containing node.
        const container = getContainingNode(state.selection);

        let trans: Transaction | undefined;
        if (container === undefined) return false;

        const { name } = container.type

        if (name === "input" || name === "hint" || name === "doc") {
            // `Easy` insertion since we can just insert directly above or below the selection.
            trans = insertionFunction(state, state.tr, latexNodeType);
        } else if (name === "coqblock" || name === "coqdoc") {
            // More difficult insertion since we have to `escape` the current coqblock.
            const { start, end } = traverseUpAndReturnFirstWithName(state, "coqblock");
            trans = state.tr.insert(place == InsertionPlace.Above ? start : end, latexNodeType.create());
        }

            // Dispatch the transaction when dispatch is given and transaction is not undefined.
            if (dispatch && trans) dispatch(trans);

            // Indicate successful command.
            return true;
        } else if (filef === FileFormat.RegularV) {
            // FIXME: Implement .v file case.
            return false;
        } else {
            // This command has no expected outcome when the Fileformat is unknown.
            return false;
        }
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
        // Early return when the file format equals unknown.
        if (filef === FileFormat.Unknown) return false;
        
        // Early return when inserting is not allowed. 
        if (!allowedToInsert(state)) return false;

        // Retrieve the name of the containing node of the selection.
        const name = getContainingNode(state.selection)?.type.name;
        if (name === undefined) return false;
        let trans: Transaction | undefined;
        
        if (name === "input" || name === "hint" || name === "doc") {
            // Create a new coqblock *and* coqcode cell and insert Above or Underneath the current selection.
            trans = insertionFunction(state, state.tr, coqblockNodeType, coqcodeNodeType);
        } else if (name === "coqblock" || name === "coqdoc") {

            // The following line prevents the insertion of coq blocks in a .v file when the cursor 
            //   is inside of an existing coq block. The insertion action here is ambiguous and the default
            //   behaviour is confusing, hence this type of insertion is disabled.
            if (filef === FileFormat.RegularV) return false;

            // Find the position outside of the coqblock and insert a new coqblock and coqcode cell above or underneath.
            const {start, end} = traverseUpAndReturnFirstWithName(state, "coqblock");
            const pos = place == InsertionPlace.Above ? start : end;
            trans = state.tr.insert(pos, 
                coqblockNodeType.create()).insert(pos + 1,coqcodeNodeType.create());
        }

        // If dispatch is given and transaction is set, dispatch the transaction.
        if (dispatch && trans) dispatch(trans);

            // Indicate that this command was successful.
            return true;
        } else if (filef === FileFormat.RegularV) {
            // FIXME: Implement .v file case.
            return false;
        } else {
            // This command has no expected outcome when the Fileformat is unknown.
            return false;
        }
    }
}