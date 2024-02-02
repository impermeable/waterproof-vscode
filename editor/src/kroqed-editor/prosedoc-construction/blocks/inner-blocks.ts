import { extractMathDisplayBlocks, extractCoqBlocks, extractBlocksUsingRanges, extractCoqDoc, extractMathDisplayBlocksCoqDoc } from "../block-extraction";
import { extractInterBlockRanges, sortBlocks } from "../utils";
import { Block } from "./block";
import { CoqCodeBlock, CoqMarkdownBlock, MarkdownBlock, MathDisplayBlock } from "./blocktypes";


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


export function createCoqInnerBlocks(input: string): Block[] {
    // A Coq block can contain:
    // - Coq code
    // - Coqdoc comments

    // Extract all the coqdoc comments: 
    const coqdocBlocks = extractCoqDoc(input);

    // Everything in between is coq code (including regular coq comments).
    const ranges = extractInterBlockRanges(coqdocBlocks, input);
    const coqCodeBlocks = extractBlocksUsingRanges<CoqCodeBlock>(input, ranges, CoqCodeBlock);

    // Return the sorted blocks.
    return sortBlocks([...coqdocBlocks, ...coqCodeBlocks]);
}

export function createCoqDocInnerBlocks(input: string): Block[] {
    // A Coqdoc comment can contain:
    // - Coq Markdown
    // - Math display (with single dollar signs)

    // Extract all the math display blocks: 
    const mathDisplayBlocks = extractMathDisplayBlocksCoqDoc(input);

    // Everything in between is coq markdown.
    const ranges = extractInterBlockRanges(mathDisplayBlocks, input);
    const coqMarkdownBlocks = extractBlocksUsingRanges<CoqMarkdownBlock>(input, ranges, CoqMarkdownBlock);

    // Return the sorted blocks.
    return sortBlocks([...mathDisplayBlocks, ...coqMarkdownBlocks]);
}