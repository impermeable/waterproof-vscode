import { HtmlTagInfo, OperationType, ParsedStep, StringCell } from "./types";
import { getEndHtmlTagText, getStartHtmlTagText, getTextOffset, parseFragment } from "./helper-functions";
import { ReplaceStep, ReplaceAroundStep, DocChange, WrappingDocChange } from "waterproof-editor";



export class NodeUpdate {

    /** Used to parse a step that causes nodes to be updated instead of just text */
    static nodeUpdate(step: ReplaceStep | ReplaceAroundStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        let result : ParsedStep;

        /** Get the doc change and do some error checking */
        if (step instanceof ReplaceStep) {
            // Determine operation type
            let type: OperationType = OperationType.delete;
            if (step.from == step.to) type = OperationType.insert;

            // We only support pure insertions and deletions
            if (type == OperationType.delete && step.slice.content.firstChild !== null) throw new Error(" We support ReplaceStep for nodes, but, only, as pure insertions and deletions ");

            // Check that the slice conforms to our assumptions
            if (step.slice.openStart != 0 || step.slice.openEnd != 0) throw new Error(" We do not support partial slices for ReplaceSteps");

            if (type === OperationType.delete) {
                // Is the node deletion in a valid location
                if(!startHtmlMap.has(step.from) || !endHtmlMap.has(step.to) ) throw new Error(" Mapping does not contain this position, is node inserted in middle of another node?");
                result = NodeUpdate.replaceStepDelete(step,stringBlocks,endHtmlMap,startHtmlMap);
            } else {
                result = NodeUpdate.replaceStepInsert(step,stringBlocks,endHtmlMap,startHtmlMap);
            }

        } else {
            // Replace around step in valid form
            if (step.gapFrom - step.from > 1 || step.to - step.gapTo > 1) throw new Error(" We only support ReplaceAroundSteps with a single gap");

            // Deletion ReplaceAroundstep
            if (step.slice.content.firstChild == null) {
                // Error check Deletion step
                if (!startHtmlMap.has(step.from) || !endHtmlMap.has(step.gapFrom)) throw new Error(" ReplaceAroundStep deletion is in unconventional form");
                if (!startHtmlMap.has(step.gapTo) || !endHtmlMap.has(step.to)) throw new Error(" ReplaceAroundStep deletion is in unconventional form");

                result = NodeUpdate.replaceAroundStepDelete(step,stringBlocks,endHtmlMap,startHtmlMap);
            } else if (step.slice.content.childCount == 1 && step.slice.openStart == 0 && step.slice.openEnd == 0) {
                // Error check ReplaceAroundStep insertion
                if (step.gapFrom - step.from > 0 || step.to - step.gapTo > 0 || step.insert != 1) throw new Error(" We only support ReplaceAroundStep that inserts chunk in single node");
                if (!(startHtmlMap.has(step.from) || endHtmlMap.has(step.to))) throw new Error(" Not a proper wrapping ");
                if(!(step.slice.content.firstChild.type.name == 'hint' || step.slice.content.firstChild.type.name == 'input')) throw new Error(" We only support wrapping in hints or inputs ");

                result = NodeUpdate.replaceAroundStepInsert(step,stringBlocks,endHtmlMap,startHtmlMap);
            } else {
                throw new Error(" We do not support this type of ReplaceAroundStep");
            }

        }

        return result;
    }

    private static replaceStepDelete(step: ReplaceStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        //// Determine the in text document change vscode side

        /** The resulting change of this step operation */
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }

        /** Get the starting and end tag of the block deletion */
        const startTag: HtmlTagInfo | undefined = startHtmlMap.get(step.from);
        const endTag: HtmlTagInfo | undefined = endHtmlMap.get(step.to);
        if (startTag === undefined || endTag === undefined ) throw new Error("The deleted block was not in the mapping");

        /** Determine the resulting DocChange indices */
        result.startInFile = startTag.offsetText;
        result.endInFile = endTag.offsetText;

        //// Update the mapping to reflect the new prosemirror state

        // New maps
        const newHtmlMap = new Map<number,HtmlTagInfo>();
        const newHtmlMapS = new Map<number,HtmlTagInfo>();
        const newMap = new Map<number,StringCell>();

        // The offsets that were deleted from the doc needed to update the mappings
        const proseOffset = getTextOffset(OperationType.delete,step);
        // This has an additional costs, which are taken account in the suceeding loop
        let textOffset = proseOffset;


        for (const [key, value] of endHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key > step.from) {
                if (key <= step.to) { // This block has been removed
                    // Adjust textOffset based on what has been deleted
                    textOffset += 1 - value.textCost;
                    continue;
                }
                newkey += proseOffset; newvalue.offsetText += textOffset;
                newvalue.offsetProse += proseOffset;
            }
            newHtmlMap.set(newkey,newvalue);
        }


        for (const [key, value] of startHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.from) {
                if (key < step.to) continue; // This block has been removed
                newkey += proseOffset; newvalue.offsetText += textOffset;
                newvalue.offsetProse += proseOffset;
            }
            newHtmlMapS.set(newkey,newvalue);
        }


        for(const [key,value] of stringBlocks) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.from) {
                if (key < step.to) continue; // This block has been removed
                newvalue.startProse += proseOffset;
                newkey += proseOffset;
                newvalue.startText += textOffset;
                newvalue.endProse += proseOffset;
                newvalue.endText += textOffset;
            }
            newMap.set(newkey,newvalue);
        }

        return {result, newHtmlMapS, newHtmlMap, newMap};
    }

    /** Converts a replace step that is a pure node update to a DocChange */
    private static replaceStepInsert(step: ReplaceStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }

        let newMap = new Map<number,StringCell>();
        let newHtmlMap = new Map<number,HtmlTagInfo>();
        let newHtmlMapS = new Map<number,HtmlTagInfo>();
        let final;
        let inBetweenText: string = "";
        let textIndex: number = 0;

        // Check if we are in an empty document
        if (endHtmlMap.size == 0) {
            final = parseFragment(step.slice.content);
            if (step.slice.content.firstChild!.content.firstChild !== null) inBetweenText = step.slice.content.firstChild!.content.firstChild.textContent;

            /** Compute the resulting DocChange */
            result.startInFile = 0;
            result.endInFile = 0;
            result.finalText = final.starttext + inBetweenText + final.endtext;
        } else {
            // Check whether we know of the insertion location
            if (!(startHtmlMap.has(step.from) || endHtmlMap.has(step.from))) throw new Error(" The insertion spot was not recognized, either mapping is off or a bug in code");

            const location = startHtmlMap.has(step.from) ? startHtmlMap.get(step.from) : endHtmlMap.get(step.from);

            if (location === undefined) throw new Error(" This cannot happen... ");

             /** Compute the resulting DocChange */
            result.startInFile = location?.offsetText;
            result.endInFile = location?.offsetText;
            final = parseFragment(step.slice.content);
            result.finalText = final.starttext + final.endtext;


            //// Update the existing mapping


            for(const [key,value] of stringBlocks) {
                let newkey = key; const newvalue = structuredClone(value);
                if (key >= step.from) {
                    newvalue.startProse += final.proseOffset;
                    newkey += final.proseOffset;
                    newvalue.startText += result.finalText.length;
                    newvalue.endProse += final.proseOffset;
                    newvalue.endText += result.finalText.length;
                }
                newMap.set(newkey,newvalue);
            }

            for (const [key, value] of endHtmlMap) {
                let newkey = key; const newvalue = structuredClone(value);
                if (key > step.from) {
                    newkey += final.proseOffset; newvalue.offsetText += result.finalText.length;
                    newvalue.offsetProse += final.proseOffset;
                }
                newHtmlMap.set(newkey,newvalue);
            }
            for (const [key, value] of startHtmlMap) {
                let newkey = key; const newvalue = structuredClone(value);
                if (key >= step.from) {
                    newkey += final.proseOffset; newvalue.offsetText += result.finalText.length;
                    newvalue.offsetProse += final.proseOffset;
                }
                newHtmlMapS.set(newkey,newvalue);
            }

            /** Set the location of where the edit is being made in vscode doc */
            textIndex = location.offsetText;
        }

        // Add the new cell to stringBlocks map, if a text area was inserted
        if (final.stringCell) {
            const newIndex = step.from + final.proseOffset / 2;
            // Add the new string cell
            newMap.set(newIndex, {
                startProse: newIndex,
                endProse: newIndex + result.finalText.length,
                startText: textIndex + final.starttext.length,
                endText: textIndex + final.starttext.length + inBetweenText.length,
            });
        }

        let proseIndex = step.from;
        // Add new tags
        for (let i = 0; i < final.tags.length; i++) {
            if (i == final.tags.length/2) {
                proseIndex += inBetweenText.length;
                textIndex += inBetweenText.length;
            }
            newHtmlMapS.set(proseIndex,{ offsetProse: proseIndex, offsetText: textIndex, textCost: final.tags[i].length});
            textIndex += final.tags[i].length;
            proseIndex += 1;
            newHtmlMap.set(proseIndex,{ offsetProse: proseIndex, offsetText: textIndex, textCost: final.tags[i].length});
        }
        // Sort the maps, so they are increasing in keys
        newMap = new Map([...newMap.entries()].sort((a,b) => a[0] - b[0]));
        newHtmlMap = new Map([...newHtmlMap.entries()].sort((a,b) => a[0] - b[0]));
        newHtmlMapS = new Map([...newHtmlMapS.entries()].sort((a,b) => a[0] - b[0]));

        return {result, newHtmlMapS, newHtmlMap, newMap};
    }

    /** Setups the wrapping doc change for the suceeding functions */
    private static setupWrapper() : WrappingDocChange {
        const edit1: DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        };
        const edit2: DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        };

        /** The resulting document change to document model */
        const result: WrappingDocChange = {
            firstEdit: edit1,
            secondEdit: edit2
        };
        return result;
    }

    private static replaceAroundStepDelete(step: ReplaceAroundStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        const result : WrappingDocChange = NodeUpdate.setupWrapper();

        // Update maps
        const newHtmlMap = new Map<number,HtmlTagInfo>();
        const newHtmlMapS = new Map<number,HtmlTagInfo>();
        const newMap = new Map<number,StringCell>();

        // @ts-expect-error TODO: Fix this
        result.firstEdit.startInFile = startHtmlMap.get(step.from)?.offsetText;
        // @ts-expect-error TODO: Fix this
        result.firstEdit.endInFile = endHtmlMap.get(step.gapFrom)?.offsetText;

        // @ts-expect-error TODO: Fix this
        result.secondEdit.startInFile = startHtmlMap.get(step.gapTo)?.offsetText;
        // @ts-expect-error TODO: Fix this
        result.secondEdit.endInFile = endHtmlMap.get(step.to)?.offsetText;

        for (const [key, value] of endHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key == step.gapFrom || key == step.to) continue;
            if (key >= step.gapFrom && key >= step.to) {
                // @ts-expect-error TODO: Fix this
                newkey -= 2; newvalue.offsetText -= (endHtmlMap.get(step.to)?.textCost + endHtmlMap.get(step.gapFrom)?.textCost);
                newvalue.offsetProse -= 2;
            } else if(key >= step.gapFrom) {
                // @ts-expect-error TODO: Fix this
                newkey -= 1; newvalue.offsetText -= endHtmlMap.get(step.gapFrom)?.textCost;
                newvalue.offsetProse -= 1;
            }
            newHtmlMap.set(newkey,newvalue);
        }
        for (const [key, value] of startHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key == step.from || key == step.gapTo) continue;
            if (key >= step.from && key >= step.gapTo) {
                // @ts-expect-error TODO: Fix this
                newkey -= 2; newvalue.offsetText -= (startHtmlMap.get(step.from)?.textCost + startHtmlMap.get(step.gapTo)?.textCost);
                newvalue.offsetProse -= 2;
            } else if(key >= step.from) {
                // @ts-expect-error TODO: Fix this
                newkey -= 1; newvalue.offsetText -= startHtmlMap.get(step.from)?.textCost;
                newvalue.offsetProse -= 1;
            }
            newHtmlMapS.set(newkey,newvalue);
        }

        for(const [key,value] of stringBlocks) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.gapFrom && key >= step.to) {
                newvalue.startProse -= 2; newkey -= 2;  newvalue.endProse -= 2;
                // @ts-expect-error TODO: Fix this
                newvalue.startText -= (endHtmlMap.get(step.to)?.textCost + endHtmlMap.get(step.gapFrom)?.textCost);
                // @ts-expect-error TODO: Fix this
                newvalue.endText -= (endHtmlMap.get(step.to)?.textCost + endHtmlMap.get(step.gapFrom)?.textCost);
            } else if (key >= step.gapFrom) {
                newvalue.startProse -= 1; newkey -= 1;  newvalue.endProse -= 1;
                // @ts-expect-error TODO: Fix this
                newvalue.startText -= endHtmlMap.get(step.gapFrom)?.textCost;
                // @ts-expect-error TODO: Fix this
                newvalue.endText -= endHtmlMap.get(step.gapFrom)?.textCost;
            }
            newMap.set(newkey,newvalue);
        }

        return {result, newHtmlMapS, newHtmlMap, newMap};
    }


    private static replaceAroundStepInsert(step: ReplaceAroundStep, stringBlocks: Map<number,StringCell>, endHtmlMap: Map<number,HtmlTagInfo>, startHtmlMap: Map<number,HtmlTagInfo>) : ParsedStep {
        const result : WrappingDocChange = NodeUpdate.setupWrapper();

        // Update maps
        let newHtmlMap = new Map<number,HtmlTagInfo>();
        let newHtmlMapS = new Map<number,HtmlTagInfo>();
        const newMap = new Map<number,StringCell>();

        result.firstEdit.startInFile = startHtmlMap.get(step.from)!.offsetText;
        result.firstEdit.endInFile = result.firstEdit.startInFile;

        result.secondEdit.startInFile = endHtmlMap.get(step.to)!.offsetText;
        result.secondEdit.endInFile = result.secondEdit.startInFile;

        if (step.slice.content.firstChild!.type.name == 'hint') {
            result.firstEdit.finalText = '<hint title="💡 Hint">';
            result.secondEdit.finalText = '</hint>'
        } else {
            result.firstEdit.finalText =  getStartHtmlTagText(step.slice.content.firstChild!.type.name);
            result.secondEdit.finalText =  getEndHtmlTagText(step.slice.content.firstChild!.type.name);
        }

        //// Update mappings

        for (const [key, value] of endHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key - 1 >= step.from && key - 1 >= step.to) {
                newkey += 2; newvalue.offsetText += result.firstEdit.finalText.length + result.secondEdit.finalText.length;
                newvalue.offsetProse += 2;
            } else if(key - 1 >= step.from) {
                newkey += 1; newvalue.offsetText += result.firstEdit.finalText.length;
                newvalue.offsetProse += 1;
            }
            newHtmlMap.set(newkey,newvalue);
        }
        for (const [key, value] of startHtmlMap) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.from && key >= step.to) {
                newkey += 2; newvalue.offsetText += result.firstEdit.finalText.length + result.secondEdit.finalText.length;
                newvalue.offsetProse += 2;
            } else if(key >= step.from) {
                newkey += 1; newvalue.offsetText += result.firstEdit.finalText.length;
                newvalue.offsetProse += 1;
            }
            newHtmlMapS.set(newkey,newvalue);
        }

        for(const [key,value] of stringBlocks) {
            let newkey = key; const newvalue = structuredClone(value);
            if (key >= step.from && key >= step.to) {
                newvalue.startProse += 2; newkey += 2;  newvalue.endProse += 2;
                newvalue.startText += result.firstEdit.finalText.length + result.secondEdit.finalText.length;
                newvalue.endText += result.firstEdit.finalText.length + result.secondEdit.finalText.length;
            } else if (key >= step.from) {
                newvalue.startProse += 1; newkey += 1;  newvalue.endProse += 1;
                newvalue.startText += result.firstEdit.finalText.length;
                newvalue.endText += result.firstEdit.finalText.length;
            }
            newMap.set(newkey,newvalue);
        }

        // Add the new html tags
        newHtmlMapS.set(step.from,{offsetProse: step.from, offsetText: result.firstEdit.startInFile, textCost: result.firstEdit.finalText.length});
        newHtmlMapS.set(step.to + 1,{offsetProse: step.to, offsetText: result.secondEdit.startInFile + result.firstEdit.finalText.length, textCost: result.secondEdit.finalText.length});
        newHtmlMap.set(step.from + 1,{offsetProse: step.from + 2, offsetText: result.firstEdit.startInFile + result.firstEdit.finalText.length, textCost: result.firstEdit.finalText.length});
        newHtmlMap.set(step.to + 2,{offsetProse: step.to + 2, offsetText: result.secondEdit.startInFile + result.firstEdit.finalText.length + result.secondEdit.finalText.length, textCost: result.secondEdit.finalText.length});

        newHtmlMap = new Map([...newHtmlMap.entries()].sort((a,b) => a[0] - b[0]));
        newHtmlMapS = new Map([...newHtmlMapS.entries()].sort((a,b) => a[0] - b[0]));

        return {result, newHtmlMapS, newHtmlMap, newMap};
    }
}

