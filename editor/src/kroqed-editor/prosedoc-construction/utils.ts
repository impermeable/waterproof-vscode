import { Block } from "./blocks";

/**
 * Convert a list of blocks to a prosemirror compatible node list.
 * @param blocks Input array of blocks.
 * @returns ProseMirror nodes. 
 */
export function blocksToProseMirrorNodes(blocks: Block[]) {
    return blocks.map((block) => block.toProseMirror());
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

/**
 * Map `f` over every consecutive pair from the `input` array.
 * @param input Input array. 
 * @param f Function to map over the pairs.
 * @returns The result of mapping `f` over every consecutive pair. Will return an empty array if the input array has length < 2.
 */
export function iteratePairs<ArrayType, FunctionReturnType>(input: Array<ArrayType>, f: (a: ArrayType, b: ArrayType) => FunctionReturnType) {
    return input.slice(0, -1).map((a, i) => f(a, input[i + 1]));
}

/**
 * Utility function to extract the ranges between blocks (ie. the ranges that are not covered by the blocks).
 * @param blocks The input array of block.
 * @param inputDocument The document the blocks are part of.
 * @returns The ranges between the blocks.
 */
export const extractInterBlockRanges = (blocks: Array<Block>, inputDocument: string): {from: number, to: number}[] => {
    let ranges =  iteratePairs(blocks, (blockA, blockB) => {
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