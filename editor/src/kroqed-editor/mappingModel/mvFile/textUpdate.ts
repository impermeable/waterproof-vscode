import { ReplaceStep } from "prosemirror-transform";
import { DocChange } from "../../../../../shared";
import { HtmlTagInfo, OperationType, ParsedStep, StringCell } from "./types";
import { getTextOffset } from "./helper-functions";



export class TextUpdate {

    /** This function is responsible for handling updates in prosemirror that happen exclusively as text edits and translating them to vscode text doc */
    static textUpdate(step: ReplaceStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        // Determine operation type
        let type: OperationType = OperationType.replace;
        if (step.from == step.to) type = OperationType.insert;
        if (step.slice.content.firstChild === null) type = OperationType.delete;

        // If there is more than one node in the fragment of step, throw an error
        if(step.slice.content.childCount > 1) throw new Error(" Text edit contained more text nodes than expected ");

        // Check that the slice conforms to our assumptions
        if (step.slice.openStart != 0 || step.slice.openEnd != 0) throw new Error(" We do not support partial slices for ReplaceSteps");

        // Find correct stringCell in which this step takes place

        /** Key of the stringCell in which step occurs */
        let correctCellKey = 0;

        for (const [key,_value] of stringBlocks) {
            if (key > step.from) break;
            correctCellKey = key;
        }

        /** Get the target cell */
        const targetCell: StringCell | undefined = stringBlocks.get(correctCellKey);
        if (targetCell === undefined) throw new Error(" Target cell is not in mapping!!! ");

        /** Check that the change is, indeed, happening within a stringcell */
        if (targetCell.endProse < step.from) throw new Error(" Step does not happen within cell ");

        /** The offset within the correct stringCell for the step action */ 
        const offsetBegin = step.from - targetCell.startProse;

        /** The offset within the correct stringCell for the step action */ 
        const offsetEnd = step.to - targetCell.startProse;  

        const text = step.slice.content.firstChild && step.slice.content.firstChild.text ? step.slice.content.firstChild.text : "";

        /** The resulting document change to document model */
        const result: DocChange = {
            startInFile: targetCell.startText + offsetBegin,
            endInFile: targetCell.startText + offsetEnd,
            finalText: text
        }

        //// Find updated mappings

        // Update the mapping to reflect change
        const newMap = new Map<number,StringCell>();
        const offset = getTextOffset(type,step);
        // Loop through all the stringblocks
        for(const [key,value] of stringBlocks) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= correctCellKey) {
                if (key != correctCellKey) {
                    newvalue.startProse += offset;
                    newkey += offset;
                    newvalue.startText += offset;
                }
                newvalue.endProse += offset;
                newvalue.endText += offset;
            }
            newMap.set(newkey,newvalue);
        }
        

        const newHtmlMap = new Map<number,HtmlTagInfo>();
        const newHtmlMapS = new Map<number,HtmlTagInfo>();
        for (const [key, value] of endHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key > step.from) {
                if (key <= step.to) throw new Error(" Edit did not take place in string cell ");
                newkey += offset; newvalue.offsetProse += offset;
                newvalue.offsetText += offset;
            }
            newHtmlMap.set(newkey,newvalue);
        }
        
        for (const [key, value] of startHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.to) {
                newkey += offset; newvalue.offsetProse += offset;
                newvalue.offsetText += offset;
            }
            newHtmlMapS.set(newkey,newvalue);
        }

        return {result, newHtmlMapS, newHtmlMap, newMap};
    }
}