import { extractMathDisplayBlocks, extractCoqBlocks, extractBlocksUsingRanges } from "../block-extraction";
import { extractInterBlockRanges, sortBlocks } from "../utils";
import { Block, BlockRange } from "./block";
import { MarkdownBlock } from "./blocktypes";


export function createInputAndHintInnerBlocks(input: string, innerRange: BlockRange): Block[] {
    // Since input areas and hints can both contain:
    // - coq
    // - math_display
    // - markdown   
    // This amounts to the same as steps 0.3 - 0.5 in topLevelBlocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(input, innerRange.from);
    const coqBlocks = extractCoqBlocks(input, innerRange.from);
    const markdownRanges = extractInterBlockRanges([...mathDisplayBlocks, ...coqBlocks], input, innerRange.from);
    const markdownBlocks = extractBlocksUsingRanges<MarkdownBlock>(input, markdownRanges, MarkdownBlock);
    const sorted = sortBlocks([...mathDisplayBlocks, ...coqBlocks, ...markdownBlocks]);
    return sorted;
}
