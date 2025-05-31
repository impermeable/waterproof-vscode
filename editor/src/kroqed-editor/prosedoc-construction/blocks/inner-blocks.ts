import { extractMathDisplayBlocks, extractCoqBlocks, extractBlocksUsingRanges } from "../block-extraction";
import { extractInterBlockRanges, sortBlocks } from "../utils";
import { Block } from "./block";
import { MarkdownBlock } from "./blocktypes";


export function createInputAndHintInnerBlocks(input: string): Block[] {
    // Since input areas and hints can both contain:
    // - coq
    // - math_display
    // - markdown   
    // This amounts to the same as steps 0.3 - 0.5 in topLevelBlocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(input);
    const coqBlocks = extractCoqBlocks(input);
    const markdownRanges = extractInterBlockRanges([...mathDisplayBlocks, ...coqBlocks], input);
    const markdownBlocks = extractBlocksUsingRanges<MarkdownBlock>(input, markdownRanges, MarkdownBlock);
    const sorted = sortBlocks([...mathDisplayBlocks, ...coqBlocks, ...markdownBlocks]);
    return sorted;
}
