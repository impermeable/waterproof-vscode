import { Mapping } from "./newmapping";
import { ParsedStep, OperationType } from "./types";
import { Tree, TreeNode } from "./Tree";
import { DocChange, ReplaceStep, TextUpdateError } from "@impermeable/waterproof-editor";
import { typeFromStep } from "./helper-functions";

export class TextUpdate {

    /** This function is responsible for handling updates in prosemirror that happen exclusively as text edits and translating them to vscode text doc */
    textUpdate(step: ReplaceStep, mapping: Mapping) : ParsedStep {
        // Determine operation type
        const type = typeFromStep(step);
        
        // If there is more than one node in the fragment of step, throw an error
        if(step.slice.content.childCount > 1) throw new TextUpdateError(" Text edit contained more text nodes than expected ");

        // Check that the slice conforms to our assumptions
        if (step.slice.openStart != 0 || step.slice.openEnd != 0) throw new TextUpdateError(" We do not support partial slices for ReplaceSteps");

        const tree = mapping.getMapping()

        const targetCell: TreeNode | null = tree.findNodeByProsemirrorPosition(step.from)
        if (targetCell === null) throw new TextUpdateError(" Target cell is not in mapping!!! ");

        if (targetCell === tree.root) throw new TextUpdateError(" Text can not be inserted into the root ");

        /** Check that the change is, indeed, happening within a stringcell */
        if (targetCell.prosemirrorEnd < step.from) throw new TextUpdateError(" Step does not happen within cell ");

        /** The offset within the correct stringCell for the step action */ 
        const offsetBegin = step.from - targetCell.prosemirrorStart;

        /** The offset within the correct stringCell for the step action */ 
        const offsetEnd = step.to - targetCell.prosemirrorStart;  

        const text = step.slice.content.firstChild && step.slice.content.firstChild.text ? step.slice.content.firstChild.text : "";

        const offset = getTextOffset(type,step);

        /** The resulting document change to document model */
        const result: DocChange = {
            startInFile: targetCell.innerRange.from + offsetBegin,
            endInFile: targetCell.innerRange.from + offsetEnd,
            finalText: text
        }

        const target = {start: targetCell.prosemirrorStart, end: targetCell.prosemirrorEnd };
        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= target.start && target.end <= node.prosemirrorEnd) {
                // This node is either the node we are making the text update in or a parent node
                // We only have to update the closing ranges
                node.shiftCloseOffsets(offset);
            } else if (node.prosemirrorEnd > target.end) {
                // This node is fully after the node in which we made the text update
                // We update all the ranges
                node.shiftOffsets(offset);
            }
        });

        let newTree = new Tree;
        newTree = tree;
        return {result, newTree};
    }
}

/** This gets the offset in the vscode document that is being added (then >0) or removed (then <0) */
function getTextOffset(type: OperationType, step: ReplaceStep) : number  {
    if (type == OperationType.delete) return step.from - step.to;

    /** Validate step if not a delete type */
    if (step.slice.content.firstChild === null || step.slice.content.firstChild.text === undefined) throw new TextUpdateError(" Invalid replace step " + step);

    if (type == OperationType.insert) return step.slice.content.firstChild.text?.length;

    return step.slice.content.firstChild.text?.length + step.from - step.to;
}