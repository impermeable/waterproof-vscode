import { WaterproofSchema } from "../../schema";
import { BLOCK_NAME, Block, BlockRange } from "./block";
import { code, hint, inputArea, markdown, mathDisplay } from "./schema";

const indentation = (level: number): string => "  ".repeat(level);
const debugInfo = (block: Block): string => `{range=${block.range.from}-${block.range.to}}`;

/**
 * InputAreaBlocks are the parts of the document that should be editable by students.
 * Every input area has an accompanying status to indicate whether the input area is 'correct'. 
 */
export class InputAreaBlock implements Block {
    public type = BLOCK_NAME.INPUT_AREA;
    public innerBlocks: Block[];

    /**
     * Construct a new InputAreaBlock.
     * @param stringContent Content of the input area
     * @param range The range (from position to to position in the original document) of the entire input area block, including the its tags.
     * @param innerRange The range (from position to to position in the original document) of the inner content of the input area block, excluding its tags.
     * @param childBlocks Either an array of child blocks of this input area block, or a function that constructs the child blocks given the inner range and content.
     */
    constructor( public stringContent: string, public range: BlockRange, public innerRange: BlockRange, childBlocks: Block[] | ((innerContent: string, innerRange: BlockRange) => Block[])) {
        if (typeof childBlocks === "function") {
            this.innerBlocks = childBlocks(stringContent, innerRange);
        }
        else {
            this.innerBlocks = childBlocks;
        }
    };

    toProseMirror() {
        const childNodes = this.innerBlocks.map(block => block.toProseMirror());
        return inputArea(childNodes);
    }

    // Debug print function. // FIXME: Maybe remove?
    debugPrint(level: number): void {
        console.log(`${indentation(level)}InputAreaBlock {${debugInfo(this)}} [`);
        this.innerBlocks.forEach(block => block.debugPrint(level + 1));
        console.log(`${indentation(level)}]`);
    }
}

/**
 * HintBlocks are foldable blocks that can be used to hide parts of the document by default. 
 * Useful for giving hints to students or hiding import/configuration statements from the student.
 */
export class HintBlock implements Block {
    public type = BLOCK_NAME.HINT;
    public innerBlocks: Block[];

    /**
     * Construct a new HintBlock.
     * @param stringContent Content of the hint block
     * @param title Title of the hint block (the part that is displayed in the document when folded)
     * @param range The range (from position to to position in the original document) of the entire hint block, including its tags.
     * @param innerRange The range (from position to to position in the original document) of the inner content of the hint block, excluding its tags.
     * @param childBlocks Either an array of child blocks of this hint block, or a function that constructs the child blocks given the inner range and content.
     */
    constructor( public stringContent: string, public title: string, public range: BlockRange, public innerRange: BlockRange, childBlocks: Block[] | ((innerContent: string, innerRange: BlockRange) => Block[])) {
        if (typeof childBlocks === "function") {
            this.innerBlocks = childBlocks(stringContent, innerRange);
        } else {
            this.innerBlocks = childBlocks;
        }
    };

    toProseMirror() {
        // We need to construct a hint node with a title and inner blocks.
        const childNodes = this.innerBlocks.map(block => block.toProseMirror());
        return hint(this.title, childNodes);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}HintBlock {${debugInfo(this)}} {title="${this.title}"} [`);
        this.innerBlocks.forEach(block => block.debugPrint(level + 1));
        console.log(`${indentation(level)}]`);
    }
}

/**
 * MathDisplayBlocks display LaTeX in display mode (i.e., centered and on its own line).
 */
export class MathDisplayBlock implements Block {
    public type = BLOCK_NAME.MATH_DISPLAY;
    constructor( public stringContent: string, public range: BlockRange, public innerRange: BlockRange ) {};

    toProseMirror() {
        return mathDisplay(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}MathDisplayBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}

/**
 * MarkdownBlocks contain markdown content (including inline LaTeX inside single dollars `$`).
 */
export class MarkdownBlock implements Block {
    public type = BLOCK_NAME.MARKDOWN;
    public isNewLineOnly = false;

    constructor( public stringContent: string, public range: BlockRange, public innerRange: BlockRange ) {
        if (stringContent === "\n") this.isNewLineOnly = true;
    };

    toProseMirror() {
        return markdown(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}MarkdownBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}

/**
 * CodeBlocks contain source code. 
 */
export class CodeBlock implements Block {
    public type = BLOCK_NAME.CODE;

    constructor( public stringContent: string, public prePreWhite: string, public prePostWhite: string, public postPreWhite: string, public postPostWhite : string, public range: BlockRange, public innerRange: BlockRange) {}

    toProseMirror() {
        if (this.stringContent === "") {
            // If the string content is empty, we create an empty coqcode node.
            return WaterproofSchema.nodes.code.create();
        }
        return code(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}CoqCodeBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}