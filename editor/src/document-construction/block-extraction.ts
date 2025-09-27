import { InputAreaBlock, HintBlock, MathDisplayBlock, CodeBlock, NewlineBlock } from "@impermeable/waterproof-editor";
import { createInputAndHintInnerBlocks } from "./inner-blocks";


const regexes = {
    // coq: /```coq\n([\s\S]*?)\n```/g,
    coq: /(\n)?^```coq\n([^]*?)\n?^```$(\n)?/gm,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>([\s\S]*?)<\/input-area>/g,
    input_areaV: /\(\* begin input \*\)\n([\s\S]*?)\n\(\* end input \*\)/gm,
    hint: /<hint title="([\s\S]*?)">([\s\S]*?)<\/hint>/g,
    hintV: /\(\* begin hint : ([\s\S]*?) \*\)\n([\s\S]*?)\n\(\* end hint \*\)/gm,
}

/**
 * Create input blocks from document string.
 *
 * Uses regexes to search for
 * - `<input-area>` and `</input-area>` tags (mv files)
 * - `(* begin input *)` and `(* end input *)` (v files)
 */
export function extractInputBlocks(document: string) {
    return extractInputBlocksMV(document);
}

const inputAreaTagOpenLength = "<input-area>".length;
const inputAreaTagCloseLength = "</input-area>".length;

function extractInputBlocksMV(document: string) {
    const input_areas = document.matchAll(regexes.input_area);

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        const innerRange = { from: range.from + inputAreaTagOpenLength, to: range.to - inputAreaTagCloseLength }
        return new InputAreaBlock(input_area[1], range, innerRange, createInputAndHintInnerBlocks(input_area[1], innerRange));
    });

    return inputAreaBlocks;
}

/**
 * Create hint blocks from document string.
 *
 * Uses regexes to search for
 * - `<hint title=[hint title]>` and `</hint>` tags (mv files)
 * - `(* begin hint : [hint title] *)` and `(* end hint *)` (v files)
 */
export function extractHintBlocks(document: string): HintBlock[] {
    return extractHintBlocksMV(document);
}

const hintTagOpenLength = "<hint title=\"\">".length;
const hintTagCloseLength = "</hint>".length;

function extractHintBlocksMV(document: string) {
    const hints = document.matchAll(regexes.hint);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const title = hint[1];
        const range = { from: hint.index, to: hint.index + hint[0].length };
        const innerRange = { from: range.from + hintTagOpenLength + title.length, to: range.to - hintTagCloseLength };
        return new HintBlock(hint[2], title, range, innerRange, createInputAndHintInnerBlocks(hint[2], innerRange));
    });

    return hintBlocks;
}

/**
 * Create math display blocks from document string.
 *
 * Uses regexes to search for `$$`.
 */
export function extractMathDisplayBlocks(inputDocument: string, parentOffset: number = 0) {
    const math_display = inputDocument.matchAll(regexes.math_display);
    const mathDisplayBlocks = Array.from(math_display).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index + parentOffset, to: math.index + math[0].length + parentOffset };
        const innerRange = { from: range.from + "$$".length, to: range.to - "$$".length}
        return new MathDisplayBlock(math[1], range, innerRange);
    });
    return mathDisplayBlocks;
}

const coqOpenLength = "```coq\n".length;
const coqCloseLength = "\n```".length;

/**
 * Create coq blocks from document string.
 *
 * Uses regexes to search for ```coq and ``` markers.
 */
export function extractCoqBlocks(inputDocument: string, parentOffset: number = 0): Array<CodeBlock | NewlineBlock> {
    const coq_code = Array.from(inputDocument.matchAll(regexes.coq));

    const blocks = coq_code.flatMap((coq) => {
        if (coq.index === undefined) throw new Error("Index of coq is undefined");
        
        // - coq[0] the match;
        // - coq[1] capture group 1, newline before the ```coq (if any);
        // - coq[2] ..., the content of the coq block;
        // - coq[3] ..., newline after the ``` (if any).
        // console.log(`==========\nprePreWhite: '${coq[1] == "\n"}'\nprePostWhite: '${coq[2] == "\n"}'\ncontent: '${coq[3]}'\npostPreWhite: '${coq[4] == "\n"}'\npostPostWhite: '${coq[5] == "\n"}'\n==========\n`)
        const content = coq[2];
        const newlineBefore = coq[1] == "\n";
        const newlineAfter = coq[3] == "\n";

        // Range of the whole coq block including the ```coq and ``` markers, but without the newlines before/after if any.
        const range = { from: coq.index + parentOffset + (newlineBefore ? 1 : 0), to: coq.index + parentOffset + (newlineBefore ? 1 : 0) + coq[2].length + coqOpenLength + coqCloseLength };

        // Range of the inner content of the coq block, excluding the ```coq and ``` markers.
        const innerRange = {from: range.from + coqOpenLength, to: range.to - coqCloseLength };

        const coqBlock = new CodeBlock(content, range, innerRange);

        if (newlineBefore && !newlineAfter) {
            return [new NewlineBlock({from: coq.index + parentOffset, to: coq.index + 1 + parentOffset}, {from: coq.index + parentOffset, to: coq.index + 1 + parentOffset}), coqBlock];
        } else if (!newlineBefore && newlineAfter) {
            return [coqBlock, new NewlineBlock({from: range.to, to: range.to + 1}, {from: range.to, to: range.to + 1})];
        } else if (newlineBefore && newlineAfter) {
            return [new NewlineBlock({from: coq.index + parentOffset, to: coq.index + 1 + parentOffset}, {from: coq.index + parentOffset, to: coq.index + 1 + parentOffset}), coqBlock, new NewlineBlock({from: range.to, to: range.to + 1}, {from: range.to, to: range.to + 1})];
        } else {
            return [coqBlock];
        }
    });

    return blocks;
}

// Regex for extracting the math display blocks from the coqdoc comments.
// We need a different regex here, since coq markdown uses single dollar signs for math display :)
const regexMathDisplay = /\$([\S\s]*?)\$/g;

export function extractMathDisplayBlocksCoqDoc(input: string): MathDisplayBlock[] {
    const mathDisplay = Array.from(input.matchAll(regexMathDisplay));
    const mathDisplayBlocks = Array.from(mathDisplay).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length};
        const innerRange = { from: range.from + "$$".length, to: range.to - "$$".length};
        return new MathDisplayBlock(math[1], range, innerRange);
    });
    return mathDisplayBlocks;
}