import { createCoqBlocks, createHintBlocks, createInputBlocks, createMarkdownBlocks, createMathDisplayBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { HintBlock, InputAreaBlock } from "./blocks/blocktypes";
import { extractInterBlockRanges, maskInputAndHints, sortBlocks } from "./utils";

// 0. Extract the top level blocks from the input document.
export function topLevelBlocks(inputDocument: string) {
    // There are five different 'top level' blocks, 
    // - hint
    // - input_area
    // - math_display
    // - coq
    // - markdown

    // 0.1 Extract the hint and input area blocks.
    const hintBlocks: HintBlock[] = createHintBlocks(inputDocument);
    const inputAreaBlocks: InputAreaBlock[] = createInputBlocks(inputDocument);

    // 0.2 Mask the hint and input area blocks in the input document.
    //     Done to make extraction of coq and math display easier, since 
    //     we don't have to worry about the hint and input area blocks.
    inputDocument = maskInputAndHints(inputDocument, [...hintBlocks, ...inputAreaBlocks]);

    // 0.3 Extract the coq and math display blocks.
    const mathDisplayBlocks = createMathDisplayBlocks(inputDocument);
    const coqBlocks = createCoqBlocks(inputDocument);

    // 0.4 Sort the blocks by their range.
    const blocks: Block[] = sortBlocks([...hintBlocks, ...inputAreaBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    const markdownRanges = extractInterBlockRanges(blocks, inputDocument);

    // 0.5 Extract the markdown blocks based on the ranges.
    const markdownBlocks = createMarkdownBlocks(inputDocument, markdownRanges);
    
    // 0.6 Sort the blocks and return.
    return sortBlocks([...blocks, ...markdownBlocks]);
}

