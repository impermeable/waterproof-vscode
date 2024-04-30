import { FileFormat } from "../../../../shared";
import { Block, CoqBlock, HintBlock, InputAreaBlock, MathDisplayBlock } from "./blocks";
import { CoqDocBlock, CoqMarkdownBlock, MarkdownBlock } from "./blocks/blocktypes";

const regexes = {
    // coq: /```coq\n([\s\S]*?)\n```/g,
    coq: /(\r\n|\n)?^```coq(\r\n|\n)([^]*?)(\r\n|\n)?^```$(\r\n|\n)?/gm,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>([\s\S]*?)<\/input-area>/g,
    input_areaV: /\(\* begin input \*\)([\s\S]*?)\(\* end input \*\)/gm,
    hint: /<hint title="([\s\S]*?)">\n([\s\S]*?)\n<\/hint>/g,
    hintV: /\(\* begin hint : ([\s\S]*?) \*\)\n([\s\S]*?)\n\(\* end hint \*\)/gm,
}

/**
 * Create input blocks from document string. 
 * 
 * Uses regexes to search for 
 * - `<input-area>` and `</input-area>` tags (mv files)
 * - `(* begin input *)` and `(* end input *)` (v files)
 */
export function extractInputBlocks(document: string, fileFormat: FileFormat = FileFormat.MarkdownV) {
    if (fileFormat === FileFormat.RegularV) {
        return extractInputBlocksV(document);
    }
    return extractInputBlocksMV(document);
}

function extractInputBlocksMV(document: string) {
    const input_areas = document.matchAll(regexes.input_area);

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        return new InputAreaBlock(input_area[1], range);
    });

    return inputAreaBlocks;
}

function extractInputBlocksV(document: string) {
    const input_areas = document.matchAll(regexes.input_areaV);

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        return new InputAreaBlock("```coq\n" + input_area[1] + "\n```", range);
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
export function extractHintBlocks(document: string, fileFormat: (FileFormat.MarkdownV | FileFormat.RegularV) = FileFormat.MarkdownV): HintBlock[] {

    if (fileFormat === FileFormat.RegularV) {
        return extractHintBlocksV(document);
    }
    return extractHintBlocksMV(document);
}

function extractHintBlocksMV(document: string) {
    const hints = document.matchAll(regexes.hint);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const range = { from: hint.index, to: hint.index + hint[0].length };
        return new HintBlock(hint[2], hint[1], range);
    });

    return hintBlocks;
}

function extractHintBlocksV(document: string) {
    const hints = document.matchAll(regexes.hintV);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const range = { from: hint.index, to: hint.index + hint[0].length };
        // This is incorrect as we should wrap the content part in a coqblock.
        return new HintBlock(`\`\`\`coq\n${hint[2]}\n\`\`\``, hint[1], range);
    });

    return hintBlocks;
}

/**
 * Create math display blocks from document string.
 * 
 * Uses regexes to search for `$$`.
 */
export function extractMathDisplayBlocks(inputDocument: string) {
    const math_display = inputDocument.matchAll(regexes.math_display);
    const mathDisplayBlocks = Array.from(math_display).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length };
        return new MathDisplayBlock(math[1], range);
    });
    return mathDisplayBlocks;
}

/**
 * Create coq blocks from document string.
 * 
 * Uses regexes to search for ```coq and ``` markers.	
 */
export function extractCoqBlocks(inputDocument: string) {
    const coq_code = Array.from(inputDocument.matchAll(regexes.coq));

    const coqBlocks = coq_code.map((coq) => {
        if (coq.index === undefined) throw new Error("Index of coq is undefined");
        const range = { from: coq.index, to: coq.index + coq[0].length };
        // TODO: Documentation for this: 
        // - coq[0] the match;
        // - coq[1] capture group 1, prePreWhite;
        // - coq[2] ..., prePostWhite;
        // - coq[3] ..., the content of the coq block;
        // - coq[4] ..., postPreWhite;
        // - coq[5] ..., postPostWhite;
        // console.log(`==========\nprePreWhite: '${coq[1] == "\n"}'\nprePostWhite: '${coq[2] == "\n"}'\ncontent: '${coq[3]}'\npostPreWhite: '${coq[4] == "\n"}'\npostPostWhite: '${coq[5] == "\n"}'\n==========\n`)
        const content = coq[3];
        const prePreWhite = coq[1] == "\n" ? "newLine" : "";
        const prePostWhite = coq[2] == "\n" ? "newLine" : "";
        const postPreWhite = coq[4] == "\n" ? "newLine" : "";
        const postPostWhite = coq[5] == "\n" ? "newLine" : "";

        return new CoqBlock(content, prePreWhite, prePostWhite, postPreWhite, postPostWhite, range);
    });
    return coqBlocks;
}

/**
 * Create blocks based on ranges.
 * 
 * Extracts the text content of the ranges and creates blocks from them.
 */
export function extractBlocksUsingRanges<BlockType extends Block>(
    inputDocument: string, 
    ranges: {from: number, to: number}[], 
    BlockConstructor: new (content: string, range: { from: number, to: number }) => BlockType ): BlockType[] 
{
    const blocks = ranges.map((range) => {
        const content = inputDocument.slice(range.from, range.to);
        return new BlockConstructor(content, range);
    }).filter(block => {
        return block.range.from !== block.range.to;
    });
    return blocks;
}


// Regex used for extracting the coqdoc comments from the coqdoc block.
// Info: https://coq.inria.fr/doc/refman/using/tools/coqdoc.html
// FIXME: This regex needs some attention. I'm especially unsure of the space before the closing `*)`.
// const coqdocRegex = /\(\*\*(?: |\n)([\s\S]*?)\*\)/g;
const coqdocRegex = /(\r\n|\n)?^\(\*\* ([^]*?)\*\)$(\r\n|\n)?/gm
export function extractCoqDoc(input: string): CoqDocBlock[] {
    const comments = Array.from(input.matchAll(coqdocRegex));
    const coqDocBlocks = Array.from(comments).map((comment) => {
        if (comment.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: comment.index, to: comment.index + comment[0].length};

        const content = comment[2];
        const preWhite = comment[1] == "\n" ? "newLine" : "";
        const postWhite = comment[3] == "\n" ? "newLine" : "";

        return new CoqDocBlock(content, preWhite, postWhite, range);
    });


    // TODO: Is there a better location for this?
    const pruned = coqDocBlocks.filter(block => {
        return block.range.from !== block.range.to; 
    });

    return pruned;
}

// Regex for extracting the math display blocks from the coqdoc comments.
// We need a different regex here, since coq markdown uses single dollar signs for math display :)
const regexMathDisplay = /\$([\S\s]*?)\$/g;

export function extractMathDisplayBlocksCoqDoc(input: string): MathDisplayBlock[] {
    const mathDisplay = Array.from(input.matchAll(regexMathDisplay));
    const mathDisplayBlocks = Array.from(mathDisplay).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length};
        return new MathDisplayBlock(math[1], range);
    });
    return mathDisplayBlocks;
}