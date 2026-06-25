import {
  Block,
  BlockRange,
  MarkdownBlock,
  utils,
} from "@impermeable/waterproof-editor";
import {
  extractMathDisplayBlocks,
  extractRocqBlocks,
} from "./block-extraction";

export function createInputAndHintInnerBlocks(
  input: string,
  innerRange: BlockRange,
): Block[] {
  // Since input areas and hints can both contain:
  // - coq
  // - math_display
  // - markdown
  // This amounts to the same as steps 0.3 - 0.5 in topLevelBlocks.
  const mathDisplayBlocks = extractMathDisplayBlocks(input, innerRange.from);
  const rocqBlocks = extractRocqBlocks(input, innerRange.from);
  const markdownRanges = utils.extractInterBlockRanges(
    [...mathDisplayBlocks, ...rocqBlocks],
    input,
    innerRange.from,
  );
  const markdownBlocks = utils.extractBlocksUsingRanges<MarkdownBlock>(
    input,
    markdownRanges,
    MarkdownBlock,
    innerRange.from,
  );
  const sorted = utils.sortBlocks([
    ...mathDisplayBlocks,
    ...rocqBlocks,
    ...markdownBlocks,
  ]);
  return sorted;
}
