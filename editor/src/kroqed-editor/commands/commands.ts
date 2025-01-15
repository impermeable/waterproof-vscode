import { Node, NodeRange, Schema } from "prosemirror-model";
import { Command, EditorState, NodeSelection, TextSelection, Transaction } from "prosemirror-state";
import { FileFormat } from "../../../../shared";
import { insertAbove, insertUnder } from "./command-helpers";
import { InsertionPlace } from "./types";
import { getCoqInsertCommand, getLatexInsertCommand, getMdInsertCommand } from "./insert-command";
import { EditorView } from "prosemirror-view";
import { liftTarget } from "prosemirror-transform";

/**
 * Get the insertion function needed for insertion at `place`.
 * @param place The place to insert at: Above or Underneath.
 * @returns The insertion function corresponding to `place`.
 */
function getInsertionFunction(place: InsertionPlace) {
    return place == InsertionPlace.Above ? insertAbove : insertUnder;
}

//// COQ ////

/*
    A coq cell is always the content of a coqblock (direct child)
    Coqblocks are children of 
    - A cell; 
    - Containers (input, hints)
*/

/**
 * Creates a command that creates a new coq cell above/underneath the currently selected node.
 * @param schema The schema to use
 * @param filef The format of the currently opened file.
 * @param insertionPlace The place to insert the new node into: Underneath or Above the current node.
 * @returns The `Command`.
 */
export function cmdInsertCoq(schema: Schema, filef: FileFormat, insertionPlace: InsertionPlace): Command {
    // Get node types for coqblock container and coqcode cell from the schema.
    const coqblockNodeType = schema.nodes["coqblock"];
    const coqcodeNodeType = schema.nodes["coqcode"];
    // Return a command with the correct insertion place and function.
    return getCoqInsertCommand(filef, getInsertionFunction(insertionPlace), insertionPlace, coqblockNodeType, coqcodeNodeType);
}

//// MARKDOWN //// 

/*
    Markdown cells (or coqdoc syntax) are either the content of
    - cells or; 
    - containers (hints, input, )

    The working of this command depends on the fileformat of the file that is currently 
    being edited. 
    If the file is .mv then we want to open a new markdown block (as a top level node)
    Otherwise, if the file is .v, we want to open a new coqdoc (if necessary) and add a new
    coqdoc markdown (abbreviated as coqdown).
*/

/**
 * Creates a command that creates a new markdown cell underneath/above the currently selected node.
 * @param schema The schema to use
 * @param filef The fileformat of the file currently opened.
 * @param insertionPlace The place to insert at: Above or Underneath current node.
 * @returns The `Command`.
 */
export function cmdInsertMarkdown(schema: Schema, filef: FileFormat, insertionPlace: InsertionPlace): Command {
    // Retrieve the node types for both markdown and coqdoc markdown (coqdown) from the schema.
    const mdNodeType = schema.nodes["markdown"];
    
    // Strictly speaking we don't conform to existing type because of our own nodes
    // @ts-expect-error
    const coqMdNodeType = schema.node["coqdown"];
    // Return a command with the correct insertion command and place.
    return getMdInsertCommand(filef, getInsertionFunction(insertionPlace), 
        insertionPlace, mdNodeType, coqMdNodeType);
}

//// DISPlAY MATH //// 

/*
    Display Math nodes are either cell contents or container contents. 
    -> Containers are hints and inputs.
*/

/**
 * Returns a command that inserts a new Display Math cell above/underneath the currently selected cell.
 * @param schema The schema in use.
 * @param filef The file format of the current file.
 * @param insertionPlace The place to insert the node at Above or Underneath the current node.
 * @returns The `Command`
 */
export function cmdInsertLatex(schema: Schema, filef: FileFormat, insertionPlace: InsertionPlace): Command {
    // Get latex node type from the schema.
    const latexNodeType = schema.nodes["math_display"];
    // Return the command with correct insertion place.
    return getLatexInsertCommand(filef, getInsertionFunction(insertionPlace), insertionPlace, latexNodeType);
}

export const liftWrapper: Command = (state: EditorState, dispatch?: ((tr: Transaction) => void), view?: EditorView): boolean => {
    const sel = state.selection;

    if (sel instanceof NodeSelection) {
        const name = sel.node.type.name;
        if (name === "hint" || name === "input") {
            // Hardcoded +1 and -1 are here to move the selection into the input/hint. 
            // The hardcoded depth 1 is the depth of a hint or an input area node type.
            const range = new NodeRange(state.doc.resolve(sel.from + 1), state.doc.resolve(sel.to - 1), 1);

            const target = liftTarget(range);

            if (target === null) return false;

            if (dispatch) dispatch(state.tr.lift(range, target).scrollIntoView());

            return true;
        }
    }

    return false;
}