import { Block, BlockRange, MarkdownBlock, utils } from "@impermeable/waterproof-editor";
import { extractMathDisplayBlocks, extractCoqBlocks } from "./block-extraction";


export function createInputAndHintInnerBlocks(input: string, innerRange: BlockRange): Block[] {
    // Since input areas and hints can both contain:
    // - coq
    // - math_display
    // - markdown
    // This amounts to the same as steps 0.3 - 0.5 in topLevelBlocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(input, innerRange.from);
    const coqBlocks = extractCoqBlocks(input, innerRange.from);
    const markdownRanges = utils.extractInterBlockRanges([...mathDisplayBlocks, ...coqBlocks], input, innerRange.from);
    const markdownBlocks = utils.extractBlocksUsingRanges<MarkdownBlock>(input, markdownRanges, MarkdownBlock);
    const sorted = utils.sortBlocks([...mathDisplayBlocks, ...coqBlocks, ...markdownBlocks]);
    return sorted;
}
