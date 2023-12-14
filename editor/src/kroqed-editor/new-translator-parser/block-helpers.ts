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