import { Block, HintBlock, InputAreaBlock, MarkdownBlock, utils } from "@impermeable/waterproof-editor";
import { extractCoqBlocks, extractHintBlocks, extractInputBlocks, extractMathDisplayBlocks } from "./block-extraction";

// 0A. Extract the top level blocks from the input document.
export function topLevelBlocksMV(inputDocument: string): Block[] {
    // There are five different 'top level' blocks, 
    // - hint
    // - input_area
    // - math_display
    // - coq
    // - markdown

    // 0A.1 Extract the hint and input area blocks.
    const hintBlocks: HintBlock[] = extractHintBlocks(inputDocument);
    const inputAreaBlocks: InputAreaBlock[] = extractInputBlocks(inputDocument);

    // 0A.2 Mask the hint and input area blocks in the input document.
    //     Done to make extraction of coq and math display easier, since 
    //     we don't have to worry about the hint and input area blocks.
    inputDocument = utils.maskInputAndHints(inputDocument, [...hintBlocks, ...inputAreaBlocks]);

    // 0A.3 Extract the coq and math display blocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(inputDocument, 0);
    const coqBlocks = extractCoqBlocks(inputDocument);

    // 0A.4 Sort the blocks by their range.
    const blocks: Block[] = utils.sortBlocks([...hintBlocks, ...inputAreaBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    const markdownRanges = utils.extractInterBlockRanges(blocks, inputDocument);

    // 0A.5 Extract the markdown blocks based on the ranges.
    const markdownBlocks = utils.extractBlocksUsingRanges<MarkdownBlock>(inputDocument, markdownRanges, MarkdownBlock);
    
    // Note: Blocks parse their own inner blocks.

    // 0A.6 Prune empty blocks.
    const allBlocks = utils.sortBlocks([...blocks, ...markdownBlocks]);

    // 0A.6 Sort the blocks and return.
    return allBlocks;
}

