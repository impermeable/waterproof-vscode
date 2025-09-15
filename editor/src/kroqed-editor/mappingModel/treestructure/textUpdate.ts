import { ReplaceStep } from "@impermeable/waterproof-editor";
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

        let tree = mapping.getMapping()

        const targetCell: TreeNode | null = tree.findNodeByProsemirrorPosition(step.from)
        if (targetCell === null) throw new Error(" Target cell is not in mapping!!! ");

        console.log(targetCell)
        console.log("test")

        /** Check that the change is, indeed, happening within a stringcell */
        if (targetCell.prosemirrorEnd < step.from) throw new Error(" Step does not happen within cell ");

        /** The offset within the correct stringCell for the step action */ 
        const offsetBegin = step.from - targetCell.prosemirrorStart;

        /** The offset within the correct stringCell for the step action */ 
        const offsetEnd = step.to - targetCell.prosemirrorStart;  

        const text = step.slice.content.firstChild && step.slice.content.firstChild.text ? step.slice.content.firstChild.text : "";

                /** The resulting document change to document model */
        const result: DocChange = {
            startInFile: targetCell.originalStart + offsetBegin,
            endInFile: targetCell.originalStart + offsetEnd,
            finalText: text
        }

        console.log(result)

        console.log("test")
        

        const offset = getTextOffset(type,step);

        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= targetCell.prosemirrorStart && node.prosemirrorEnd <= targetCell.prosemirrorEnd) {
                // Remove the node from the tree
                node.prosemirrorEnd += offset;
                node.originalEnd += offset;
                node.stringContent = text
            }
            if (node.prosemirrorStart > targetCell.prosemirrorStart) {
                node.prosemirrorStart += offset;
                node.prosemirrorEnd += offset;
                node.originalStart += offset;
                node.originalEnd += offset;
            }
        });
        let newTree = new Tree;
        newTree = tree;
        console.log(tree)
        console.log("test")
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