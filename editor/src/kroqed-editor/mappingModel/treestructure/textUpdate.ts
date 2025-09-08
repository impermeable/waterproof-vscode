import { ReplaceStep } from "prosemirror-transform";
import { DocChange } from "../../../../../shared";
import { TextDocMappingNew } from "./newmapping";
import { ParsedStep, OperationType } from "./types";
import { Tree, TreeNode } from "./Tree";




export class TextUpdate {

    /** This function is responsible for handling updates in prosemirror that happen exclusively as text edits and translating them to vscode text doc */
    static textUpdate(step: ReplaceStep, mapping: TextDocMappingNew) : ParsedStep {
        // Determine operation type
        let type: OperationType = OperationType.replace;
        if (step.from == step.to) type = OperationType.insert;
        if (step.slice.content.firstChild === null) type = OperationType.delete;


        // If there is more than one node in the fragment of step, throw an error
        if(step.slice.content.childCount > 1) throw new Error(" Text edit contained more text nodes than expected ");

        // Check that the slice conforms to our assumptions
        if (step.slice.openStart != 0 || step.slice.openEnd != 0) throw new Error(" We do not support partial slices for ReplaceSteps");

        const tree = mapping.getMapping()

        const targetCell: TreeNode | null = tree.findNodeByProsemirrorPosition(step.from)
        if (targetCell === null) throw new Error(" Target cell is not in mapping!!! ");

        /** Check that the change is, indeed, happening within a stringcell */
        if (targetCell.prosemirrorEnd < step.from) throw new Error(" Step does not happen within cell ");

        /** The offset within the correct stringCell for the step action */ 
        const offsetBegin = step.from - targetCell.prosemirrorStart;

        /** The offset within the correct stringCell for the step action */ 
        const offsetEnd = step.to - targetCell.prosemirrorStart;  

        let resultText = ""

        const offset = getTextOffset(type,step);

        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= targetCell.prosemirrorStart && node.prosemirrorEnd <= targetCell.prosemirrorEnd) {
                // Remove the node from the tree
                // console.log(node.prosemirrorEnd)
                // console.log(node.originalEnd)

                // Update only if it's a leaf
                const localOffsetBegin = step.from - node.prosemirrorStart;
                const localOffsetEnd   = step.to   - node.prosemirrorStart;

                const insertedText = step.slice.content.firstChild?.text ?? "";

                node.stringContent =
                    node.stringContent.slice(0, localOffsetBegin) +
                    insertedText +
                    node.stringContent.slice(localOffsetEnd);

                resultText = node.stringContent
                    
                node.prosemirrorEnd += offset;
                node.originalEnd += offset;
            } else if (node.prosemirrorStart > targetCell.prosemirrorStart) {
                node.prosemirrorStart += offset;
                node.prosemirrorEnd += offset;
            } else if (node.originalStart > targetCell.originalStart) {
                node.originalStart += offset;
                node.originalEnd += offset;
            } 
        });

        /** The resulting document change to document model */
        const result: DocChange = {
            startInFile: targetCell.originalStart + offsetBegin,
            endInFile: targetCell.originalStart + offsetEnd,
            finalText: resultText
        }

        let newTree = new Tree;
        newTree = tree;
        return {result, newTree};
    }



}
/** This gets the offset in the vscode document that is being added (then >0) or removed (then <0) */
function getTextOffset(type: OperationType, step: ReplaceStep) : number  {
    if (type == OperationType.delete) return step.from - step.to;

    /** Validate step if not a delete type */
    if (step.slice.content.firstChild === null || step.slice.content.firstChild.text === undefined) throw new Error(" Invalid replace step " + step);

    if (type == OperationType.insert) return step.slice.content.firstChild.text?.length;

    return step.slice.content.firstChild.text?.length + step.from - step.to;
}