import { sortBlocks } from "./block-helpers";
import { createHintBlocks, createInputBlocks, createMathDisplayBlocks, createCoqBlocks, createMarkdownBlocks } from "./block-parsing";
import { Block } from "./blocks";

export function constructBlocks(inputDocument: string, skipHintAndInput: boolean = false) {
    let hintBlocks: Block[] = [];
    let inputAreaBlocks: Block[] = [];
    if (!skipHintAndInput) {
        hintBlocks = createHintBlocks(inputDocument);
        inputAreaBlocks = createInputBlocks(inputDocument);
    } else {
        hintBlocks = [];
        inputAreaBlocks = [];
    }

    // We have the input and hint blocks at this point. 
    // Find the math_diplays and coq code blocks.
    const mathDisplayBlocks = createMathDisplayBlocks(inputDocument);
    const coqBlocks = createCoqBlocks(inputDocument);

    // Sort the blocks
    const sortedBlocks = sortBlocks([...inputAreaBlocks, ...hintBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    const macro = (input, f) => input.slice(1).map((v, i) => f(input.slice(i, i + 2)));
    let ranges = macro(sortedBlocks, (blocks: Block[]) => {
        const [blockA, blockB] = blocks;
        return {from: blockA.range.to, to: blockB.range.from};
    });

    // Add first range if it exists
    if (sortedBlocks.length > 0 && sortedBlocks[0].range.from > 0) ranges = [{from: 0, to: sortedBlocks[0].range.from}, ...ranges];
    // Add last range if it exists
    if (sortedBlocks.length > 0 && sortedBlocks[sortedBlocks.length - 1].range.to < inputDocument.length) ranges = [...ranges, {from: sortedBlocks[sortedBlocks.length - 1].range.to, to: inputDocument.length}];

    // In the case that we have markdown only we need to add them as well.
    if (sortedBlocks.length === 0) ranges = [{from: 0, to: inputDocument.length}];

    const markdownBlocks = createMarkdownBlocks(inputDocument, ranges);
    const allBlocks = sortBlocks([...sortedBlocks, ...markdownBlocks]);
    return allBlocks;
}