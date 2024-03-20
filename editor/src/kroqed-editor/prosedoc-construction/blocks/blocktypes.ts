import { BLOCK_NAME, Block, BlockRange } from "./block";
import { createCoqDocInnerBlocks, createCoqInnerBlocks, createInputAndHintInnerBlocks } from "./inner-blocks";
import { coqCode, coqDoc, coqMarkdown, coqblock, hint, inputArea, markdown, mathDisplay, text } from "./schema";
import { Node as ProseNode } from "prosemirror-model";

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

export class CoqBlock implements Block {
    public type = BLOCK_NAME.COQ;
    public innerBlocks: Block[];

    constructor( public stringContent: string, public prePreWhite: string, public prePostWhite: string, public postPreWhite: string, public postPostWhite : string, public range: BlockRange ) {
        this.innerBlocks = createCoqInnerBlocks(stringContent);
    };

    toProseMirror() {
        const childNodes = this.innerBlocks.map(block => block.toProseMirror());
        return coqblock(childNodes, this.prePreWhite, this.postPostWhite);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}CoqBlock {${debugInfo(this)}} [`);
        this.innerBlocks.forEach(block => block.debugPrint(level + 1));
        console.log(`${indentation(level)}]`);
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

export class CoqDocBlock implements Block {
    public type = BLOCK_NAME.COQ_DOC;
    public innerBlocks: Block[];

    constructor( public stringContent: string, public preWhite: string, public postWhite: string, public range: BlockRange ) {
        this.innerBlocks = createCoqDocInnerBlocks(stringContent);
    };

    toProseMirror() {
        const childNodes = this.innerBlocks.map(block => block.toProseMirror());
        return coqDoc(childNodes, this.preWhite, this.postWhite);
    }

    // Debug print function.
    debugPrint(level: number = 0) {
        console.log(`${indentation(level)}CoqDocBlock {${debugInfo(this)}} [`);
        this.innerBlocks.forEach(block => block.debugPrint(level + 1));
        console.log(`${indentation(level)}]`);
    }
}

export class CoqMarkdownBlock implements Block {
    public type = BLOCK_NAME.COQ_MARKDOWN;

    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        // We need to do some preprocessing on the string content, since coq markdown uses % for inline math.
        return coqMarkdown(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}CoqMarkdownBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}

export class CoqCodeBlock implements Block {
    public type = BLOCK_NAME.COQ_CODE;

    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        return coqCode(this.stringContent);
    }

    // Debug print function.
    debugPrint(level: number): void {
        console.log(`${indentation(level)}CoqCodeBlock {${debugInfo(this)}}: {${this.stringContent.replaceAll("\n", "\\n")}}`);
    }
}