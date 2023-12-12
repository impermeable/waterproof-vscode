import { Node as PNode } from "prosemirror-model";
import { TheSchema } from "../kroqed-schema";
import { coq, markdown, mathDisplay, text } from "./prosemirror-document-helpers";

export enum BLOCK_NAME {
    coq = "coq",
    math_display = "math_display", 
    input_area = "input_area",
    hint = "hint", 
    markdown = "markdown"
}

interface BlockRange {
    to: number,
    from: number
}

interface Block {
    name: string;
    content: string;
    range: BlockRange;

    toProseMirror(): PNode;
}

export const isCoqBlock = (block: Block): block is CoqBlock => block.name === BLOCK_NAME.coq;

class CoqBlock implements Block {
    public name = BLOCK_NAME.coq;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return coq(this.content);
    }
}

export const isMathDisplayBlock = (block: Block): block is MathDisplayBlock => block.name === BLOCK_NAME.math_display;

class MathDisplayBlock implements Block {
    public name = BLOCK_NAME.math_display;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return mathDisplay(this.content);
    }
}

export const isInputAreaBlock = (block: Block): block is InputAreaBlock => block.name === BLOCK_NAME.input_area;

class InputAreaBlock implements Block {
    public name = BLOCK_NAME.input_area;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return text(this.content);
    }
}

export const isHintBlock = (block: Block): block is HintBlock => block.name === BLOCK_NAME.hint;

class HintBlock implements Block {
    public name = BLOCK_NAME.hint;
    constructor( public content: string, public title: string, public range: BlockRange ) {};

    toProseMirror() {
        return text(this.content);
    }
}

class MarkdownBlock implements Block {
    public name = BLOCK_NAME.markdown;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return markdown(this.content);
    }
}



export function testingTest(inputDocument: string) {
    const { hintBlocks, inputAreaBlocks } = hintAndInputBlocks(inputDocument);

    // We have the input and hint blocks at this point. 
    // Find the math_diplays and coq code blocks.
    const mathDisplayBlocks = createMathDisplayBlocks(inputDocument);
    const coqCodeBlocks = createCoqBlocks(inputDocument);

}

export function createMathDisplayBlocks(inputDocument: string) {
    const math_display = inputDocument.matchAll(regexes.math_display);
    const mathDisplayBlocks = Array.from(math_display).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length };
        return new MathDisplayBlock(math[1], range);
    });
    return mathDisplayBlocks;
}

export function createCoqBlocks(inputDocument: string) {
    const coq_code = inputDocument.matchAll(regexes.coq);
    const coqBlocks = Array.from(coq_code).map((coq) => {
        if (coq.index === undefined) throw new Error("Index of coq is undefined");
        const range = { from: coq.index, to: coq.index + coq[0].length };
        return new CoqBlock(coq[1], range);
    });
    return coqBlocks;
}

// // Extract the remaining document after the input area and hint blocks have been removed.
// export function getRemainingAfterInputAndHint(docContent: string, sortedInputAndHints: Block[]) {
//     const start = 0;
//     const end = docContent.length;
//     let remaining = docContent;

// }

const regexes = {
    coq: /```coq\n([\s\S]*?)\n```/g,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>\n([\s\S]*?)\n<\/input-area>/g,
    hint: /<hint title="([\s\S]*?)">\n([\s\S]*?)\n<\/hint>/g,
    coqdoc: /\(\*\* ([\s\S]*?) \*\)/g
}

/**
 * Helper function to sort block type objects. Will sort based on the range object of the block. 
 * Sorts in ascending (`range.from`) order.
 * @param blocks Blocks to sort.
 * @returns Sorted array of blocks.
 */
export function sortBlocks(blocks: Block[]) {
    return blocks.sort((a, b) => a.range.from - b.range.from);
}

export function hintAndInputBlocks(document: string) {
    const hints = document.matchAll(regexes.hint);
    const input_areas = document.matchAll(regexes.input_area);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const range = { from: hint.index, to: hint.index + hint[0].length };
        return new HintBlock(hint[2], hint[1], range);
    });

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        return new InputAreaBlock(input_area[1], range);
    });

    return {inputAreaBlocks, hintBlocks};
}