import { WaterproofSchema } from "../../schema";
import { BLOCK_NAME, Block, BlockRange } from "./block";
import { createInputAndHintInnerBlocks } from "./inner-blocks";
import { code, hint, inputArea, markdown, mathDisplay } from "./schema";

const indentation = (level: number): string => "  ".repeat(level);
const debugInfo = (block: Block): string => `{range=${block.range.from}-${block.range.to}}`;

export class InputAreaBlock implements Block {
    public type = BLOCK_NAME.INPUT_AREA;
    public innerBlocks: Block[];

    constructor( public stringContent: string, public range: BlockRange ) {
        this.innerBlocks = createInputAndHintInnerBlocks(stringContent);
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

export class HintBlock implements Block {
    public type = BLOCK_NAME.HINT;
    public innerBlocks: Block[];

    // Note: Hint blocks have a title attribute.
    constructor( public stringContent: string, public title: string, public range: BlockRange ) {
        this.innerBlocks = createInputAndHintInnerBlocks(stringContent);
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

export class MathDisplayBlock implements Block {
    public type = BLOCK_NAME.MATH_DISPLAY;
    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        return mathDisplay(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}MathDisplayBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}

export class MarkdownBlock implements Block {
    public type = BLOCK_NAME.MARKDOWN;
    public isNewLineOnly = false;

    constructor( public stringContent: string, public range: BlockRange ) {
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

export class CodeBlock implements Block {
    public type = BLOCK_NAME.CODE;

    constructor( public stringContent: string, public prePreWhite: string, public prePostWhite: string, public postPreWhite: string, public postPostWhite : string, public range: BlockRange ) {}

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