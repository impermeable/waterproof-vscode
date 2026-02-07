import { getEndHtmlTagText, getStartHtmlTagText} from "./helper-functions";
import { StringCell, HtmlTagInfo, ParsedStep} from "./types";
import { TextUpdate } from "./textUpdate";
import { NodeUpdate } from "./nodeUpdate";
import { DocChange, ReplaceAroundStep, ReplaceStep, Step, WaterproofMapping, WrappingDocChange } from "@impermeable/waterproof-editor";


/**
 * A type to specify an HTML tag in the prosemirror content elem.
 */
interface TagInformation {
    /** The starting index of the tag in the input string */
    start: number;
    /** The ending index of the tag in the input string */
    end: number;
    /** The number of 'hidden' newlines the starting tag encodes in the original vscode document */
    preNumber: number;
    /** The number of 'hidden' newlines the ending tag encodes in the original vscode document */
    postNumber: number;
    /** The actual tag */
    content: string;
};


/**
 * We will preface this class with saying that this is most probably not 'the' smart approach. In fact,
 * it could possibly be simpler to do all this with the EditorState document node (textContent attribute).
 * However, we had thought this approach would be somewhat viable and nice for large documents, as you are not
 * sending the entire doc back and forth, but it comes at the cost of complexity.
 *
 * This class is responsible for keeping track of the mapping between the prosemirror state and the vscode Text
 * Document model
 */
export class TextDocMappingV implements WaterproofMapping {
    /** This stores the String cells of the entire document */
    private stringBlocks: Map<number, StringCell>;
    /** This stores the inverted mapping of stringBlocks  */
    private invStringBlocks: Map<number, StringCell>;
    /** This maps the AFTER prosemirror positions of all the HTML tags to positions in the textdocument */
    private endHtmlMap: Map<number, HtmlTagInfo>;
    /** This maps the BEFORE prosemirror positions of all the HTML tags to positions in the textdocument */
    private startHtmlMap: Map<number, HtmlTagInfo>;
    /** The version of the underlying textDocument */
    private _version: number;

    /** The different possible HTMLtags in kroqed-schema */
    private static HTMLtags: Set<string> = new Set<string>([
        "markdown",
        "input-area",
        "coqblock",
        "coqcode",
        "coqdoc",
        "math-display",
        "hint",
        "coqdown",
    ]);

    /**
     * Constructs a prosemirror view vsode mapping for the inputted prosemirror html elem
     *
     * @param inputString a string contatining the prosemirror content html elem
     */
    constructor(inputString: string, versionNum: number) {
        this._version = versionNum;
        this.stringBlocks = new Map<number, StringCell>();
        this.invStringBlocks = new Map<number, StringCell>();
        this.endHtmlMap = new Map<number,HtmlTagInfo>();
        this.startHtmlMap = new Map<number,HtmlTagInfo>();
        this.initialize(inputString);
    }

    //// The getters of this class

    /**
     * Returns the mapping to preserve integrity
     */
    public getMapping() {
        return this.stringBlocks
    }

    /**
     * Get the version of the underlying text document
     */
    public get version() {
        return this._version;
    }

    /** Returns the vscode document model index of prosemirror index */
    public findPosition(index: number) {
        let correctCellKey = 0;
        for (const [key,_value] of this.stringBlocks) {
            if (key > index) break;
            correctCellKey = key;
        }
        const targetCell: StringCell | undefined = this.stringBlocks.get(correctCellKey);
        if (targetCell === undefined) throw new Error(" The vscode document model index could not be found ");
        return (index - correctCellKey) + targetCell.startText;
    }

    /** Returns the prosemirror index of vscode document model index */
    public findInvPosition(index: number) {
        let correctCellKey = 0;
        for (const [key,_value] of this.invStringBlocks) {
            if (key > index) break;
            correctCellKey = key;
        }
        const targetCell: StringCell | undefined = this.invStringBlocks.get(correctCellKey);
        if (targetCell === undefined) throw new Error(" The prosemirror index could not be found ");
        return (index - correctCellKey) + targetCell.startProse;
    }

    //// The methods used to manage the mapping

    /**
     * Initializes the mapping according to the inputed html content elem
     *
     * @param inputString the string of the html elem
     */
    private initialize(inputString: string) : void {
        /** A stack to which we push starting html tags and pop them once we encounter the closing tag */
        const stack = new Array<{ tag: string, offsetPost: number}>;

        /** The current index we are at within the prosemirror content elem */
        let offsetProse: number = 0;

        /** The current index we are at within the raw vscode text document */
        let offsetText: number = 0;

        // Continue until the entire string has been parsed
        while(inputString.length > 0) {
            const next: TagInformation = TextDocMappingV.getNextHTMLtag(inputString);
            let nextCell: StringCell | undefined = undefined;

            /** The number of characters the tag `next` takes up in the raw vscode doc. */
            let textCost = 0;

            // Check whether `next` is a closing tag
            if (stack.length && stack[stack.length - 1].tag === next.content) {
                const stackTag = stack.pop();
                if (stackTag === undefined) throw new Error(" Stack returned undefined in initialization of vscode mapping");
                nextCell = {
                    startProse: offsetProse, endProse: offsetProse + next.start,
                    startText: offsetText, endText: offsetText + next.start,
                };
                textCost += stackTag.offsetPost; // Increment for the post newlines
                textCost += getEndHtmlTagText(next.content).length;
            } else { // Otherwise `next` opens a block
                stack.push({ tag: next.content, offsetPost: next.postNumber}); // Push new tag to stack
                // Add text offset based on tag
                if (next.content == "hint") textCost += inputString.slice(next.start, next.end).length;
                else textCost += getStartHtmlTagText(next.content).length;

                textCost += next.preNumber;

            }
            // Update offsets, so we are at the start of this tag
            offsetText += next.start;
            offsetProse += next.start;

            // Add start information of this tag to mapping
            this.startHtmlMap.set(offsetProse,{ offsetText: offsetText, offsetProse: offsetProse, textCost: textCost});

            // Update offsets, so we are at end of tag
            offsetText += textCost;
            offsetProse += 1;

            // Add end information of this tag to mapping
            this.endHtmlMap.set(offsetProse,{ offsetText: offsetText, offsetProse: offsetProse, textCost: textCost});

            // Check if the nextCell should be pushed
            switch(next.content) {
                case "coqcode":
                case "math-display": case "coqdown":
                    // If the nextcell is set, push it to mapping
                    if(!(nextCell === undefined)) this.stringBlocks.set(nextCell.startProse, nextCell);
                    break;
            }

            // Update the input string and cut off the processed text
            inputString = inputString.slice(next.end);

        }
        this.updateInvMapping();
    }


    /** Checks whether the step takes place exclusively within a string cell */
    private inStringCell(step: ReplaceStep | ReplaceAroundStep) : boolean {
        let correctCellKey = 0;
        for (const [key,_value] of this.stringBlocks) {
            if (key > step.from) break;
            correctCellKey = key;
        }
        const targetCell = this.stringBlocks.get(correctCellKey);
        return targetCell !== undefined && step.to <= targetCell.endProse;
    }

    /** Called whenever a step is made in the editor */
    public update(step: Step) : DocChange | WrappingDocChange {
        if (!(step instanceof ReplaceStep || step instanceof ReplaceAroundStep))
            throw new Error("Step update (in textDocMapping) should not be called with a non document changing step");

        /** Check whether the edit is a text edit and occurs within a stringcell */
        const isText: boolean = (step.slice.content.firstChild === null) ? this.inStringCell(step) : step.slice.content.firstChild.type.name === "text";

        let result : ParsedStep;

        /** Parse the step into a text document change */
        if (step instanceof ReplaceStep && isText) result = TextUpdate.textUpdate(step, this.stringBlocks, this.endHtmlMap, this.startHtmlMap);
        else result = NodeUpdate.nodeUpdate(step, this.stringBlocks, this.endHtmlMap, this.startHtmlMap);

        /** Update the mappings */
        this.startHtmlMap = result.newHtmlMapS;
        this.endHtmlMap = result.newHtmlMap;
        this.stringBlocks = result.newMap;

        /** Update the inverse mapping */
        this.updateInvMapping();

        if ('finalText' in result.result) {
            if(this.checkDocChange(result.result)) this._version++;
        } else {
            if(this.checkDocChange(result.result.firstEdit) || this.checkDocChange(result.result.secondEdit)) this._version++;
        }

        return result.result;
    }

    /** Constructs a map from stringBlocks that is indexed based on the vscode index instead of prose */
    private updateInvMapping() {
        this.invStringBlocks = new Map<number, StringCell>();
        this.stringBlocks.forEach((value, _key) => {
            this.invStringBlocks.set(value.startText, value)
        });
    }

    /**
     * This checks if the doc change actually changed the document, since vscode
     * does not register empty changes
     */
    private checkDocChange(change: DocChange) : boolean {
        if (change.endInFile === change.startInFile && change.finalText.length == 0) return false;
        return true;
    }

    /**
     * Function that returns the next valid html tag in a string.
     * Throws an error if no valid html tag is found.
     * @param The string that contains html tags
     * @returns The first valid html tag in the string and the position of this tag in the string
     */
    public static getNextHTMLtag(input: string): TagInformation {

        // Find all html tags (this is necessary for the position and for invalid matches)
        const matches = Array.from(input.matchAll(/<(\/)?([\w-]+)( [^]*?)?>/g));

        // Loop through all matches
        for (const match of matches) {

            // Check if there are no weird matches that we should throw an error on
            if (match !== null) {

                // Receive information about the matches
                const length = match[0].length;
                const start = match.index;

                // Ensure that we always have the position of the string
                if (start === undefined) {
                    throw new Error("Index cannot be null");
                }

                // Compute the end position of the tag
                const end = start + length;

                // Check if the HTML tag is a valid HTML tag in our parser
                if (TextDocMappingV.HTMLtags.has(match[2])) {

                    // For entry coqblocks we must extract more information about the starting and ending newline
                    if (match[2] === "coqblock" && match[1] == undefined) {

                        // Get the matches regarding whitespace
                        const whiteSpaceMatch = match[3]

                        // Helper variables
                        let preNum = 0
                        let postNum = 0

                        // We check for the pre whiteline in front of the first coqblock tag
                        const prePreWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/prePreWhite="(\w*?)"/g))[0]
                        if (prePreWhiteMatch != null) {

                            // If there is a newline tage we include this in preNum
                            if (prePreWhiteMatch[1] === "newLine") {
                                preNum++;
                            }
                        }

                        // We check for the post whiteline after the first coqblock tag
                        const postPreWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/prePostWhite="(\w*?)"/g))[0]
                        if (postPreWhiteMatch != null) {

                            // If there is a newline tage we include this in preNum
                            if (postPreWhiteMatch[1] === "newLine") {
                                preNum++;
                            }
                        }

                        // We check for the pre whiteline in front of the closing coqblock tag
                        const prePostWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/postPreWhite="(\w*?)"/g))[0]
                        if (prePostWhiteMatch != null) {

                            // If there is a newline tage we include this in postNum
                            if (prePostWhiteMatch[1] === "newLine") {
                                postNum++;
                            }
                        }

                        // We check for the post whiteline after the closing coqblock tag
                        const postPostWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/postPostWhite="(\w*?)"/g))[0]
                        if (postPostWhiteMatch != null) {

                            // If there is a newline tage we include this in postNum
                            if (postPostWhiteMatch[1] === "newLine") {
                                postNum++;
                            }
                        }

                        //return the resulting object
                        return {start: start, end: end, content: match[2], preNumber: preNum, postNumber: postNum}

                    // For coqdoc we repeat the same process
                    } else if ((match[2] === "coqdoc") && match[1] == undefined){

                        // Get the matches regarding whitespace
                        const whiteSpaceMatch = match[3]

                        // Helper variables
                        let preNum = 0
                        let postNum = 0

                        // Pre coqdoc newline
                        const preWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/preWhite="(\w*?)"/g))[0]
                        if (preWhiteMatch != null) {
                            if (preWhiteMatch[1] === "newLine") {
                                preNum++;
                            }
                        }

                        // Post coqdoc newline
                        const postWhiteMatch = Array.from(whiteSpaceMatch.matchAll(/postWhite="(\w*?)"/g))[0]
                        if (postWhiteMatch != null) {
                            if (postWhiteMatch[1] === "newLine") {
                                postNum++;
                            }
                        }

                        // Return the result
                        return {start: start, end: end, content: match[2], preNumber: preNum, postNumber: postNum}
                    } else  {

                        return {start: start, end: end, content: match[2], preNumber: 0, postNumber: 0}
                    }

                }
            } else {

                // WE have incountered an invalid match
                throw new Error("match is null")
            }
        }

        // We have found no valid HTML tags which means the string on input was invalid.
        throw new Error(" No tag found ");

    }


}



