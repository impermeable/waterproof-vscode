import { Fragment, ReplaceStep } from "waterproof-editor/api";
import { OperationType, textEndHTML, textStartHTML } from "./types";


//// We define helper functions used by the vscode mapping 

/** A helper function to get the in text representation (in vscode doc) of a ending tag */
export function getEndHtmlTagText(tagId: string | undefined) : string {
    if (tagId === undefined) throw new Error("In the vscode Mapping, a tag was undefined ");
    const result : string | undefined =  textEndHTML.get(tagId);
    if (result === undefined) throw new Error("In the vscode Mapping, a tag, " + tagId + ", was processed that should not be processed");
    return result;
}

/** A helper function to get the in text representation (in vscode doc) of a starting tag */
export function getStartHtmlTagText(tagId: string | undefined) : string {
    if (tagId === undefined) throw new Error("In the vscode Mapping, a tag was undefined ");
    const result : string | undefined = textStartHTML.get(tagId);
    if (result === undefined) throw new Error("In the vscode Mapping, a tag, " + tagId + ", was processed that should not be processed");
    return result;
}

/** Used to parse a prosemirror fragment into a form that can be used to update the mapping */
export function parseFragment(frag: Fragment | undefined) : {proseOffset: number, starttext: string, endtext: string, tags: Array<string>, stringCell: boolean} {
    // Error checking
    if (frag === undefined) throw new Error("Received an undfined fragment during parsing of fragment for vscode mapping");
    if (frag.childCount > 1) throw new Error("Fragment contains more children than expected");

    // Base case
    if (frag.childCount == 0) return {proseOffset: 0, starttext: "", endtext: "", tags: [], stringCell: false};

    /** Recursively get the fragment information for inner child */
    const inside = parseFragment(frag.firstChild?.content);

    let end = getEndHtmlTagText(frag.firstChild?.type.name);
    let start = getStartHtmlTagText(frag.firstChild?.type.name);

    /** Does the inner most cell of this fragment support text edits */
    let needsCell: boolean = false;

    /** Add newlines to end and start of new tags */
    switch(frag.firstChild?.type.name) {
        case "coqblock": 
            start = "\n" + start + "\n";
            end = "\n" + end + "\n";
            break;
        case "coqdoc":
            start = "\n" + start;
            end = end + "\n";
            break;
        case "math_display":
            start += "$";
            end += "$";
        // Purposeful fallthrough
        // eslint-disable-next-line no-fallthrough
        case "coqcode": 
        case "coqdown":
        case "markdown":
            needsCell = true;
            break;
        default:
            break;
    }

    // Create an array of tags
    let newTags = new Array<string>();
    if(frag.firstChild?.type.name !== "text") newTags.push(start); 
    newTags = newTags.concat(inside.tags); 
    if(frag.firstChild?.type.name !== "text") newTags.push(end);

    return {
        endtext: inside.endtext + end,
        starttext: start + inside.starttext,
        proseOffset: inside.proseOffset + ((frag.firstChild?.type.name == "text") ? 0 : 2),
        tags: newTags,
        stringCell: inside.stringCell || needsCell,
    };
}

/** This gets the offset in the vscode document that is being added (then >0) or removed (then <0) */
export function getTextOffset(type: OperationType, step: ReplaceStep) : number  {
    if (type == OperationType.delete) return step.from - step.to;

    /** Validate step if not a delete type */
    if (step.slice.content.firstChild === null || step.slice.content.firstChild.text === undefined) throw new Error(" Invalid replace step " + step);

    if (type == OperationType.insert) return step.slice.content.firstChild.text?.length;

    return step.slice.content.firstChild.text?.length + step.from - step.to;
}