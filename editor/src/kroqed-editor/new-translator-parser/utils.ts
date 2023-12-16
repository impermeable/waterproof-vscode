import { Block } from "./blocks";

const mapTwo = (input, f) => input.slice(1).map((v, i) => f(input.slice(i, i + 2)));

export const extractInterBlockRanges = (blocks: Array<Block>, inputDocument: string) => {
    let ranges =  mapTwo(blocks, ([blockA, blockB]) => {
        return { from: blockA.range.to, to: blockB.range.from };
    });

    // Add first range if it exists
    if (blocks.length > 0 && blocks[0].range.from > 0) ranges = [{from: 0, to: blocks[0].range.from}, ...ranges];
    // Add last range if it exists
    if (blocks.length > 0 && blocks[blocks.length - 1].range.to < inputDocument.length) ranges = [...ranges, {from: blocks[blocks.length - 1].range.to, to: inputDocument.length}];

    // If there are no blocks found then we add the rest as a range.
    if (blocks.length === 0 && inputDocument.length > 0) ranges = [{from: 0, to: inputDocument.length}];

    return ranges;
}