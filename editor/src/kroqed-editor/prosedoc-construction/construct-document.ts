import { createCoqBlocks, createHintBlocks, createInputBlocks, createMathDisplayBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { HintBlock, InputAreaBlock } from "./blocks/blocktypes";
import { extractInterBlockRanges, maskInputAndHints, sortBlocks } from "./utils";

/**
 * Construct prosemirror document from a string input. 
 * @param inputDocument The input document.
 */
export function createProseDocument(inputDocument: string) {
    // There are five different 'top level' blocks, 
    // - hint
    // - input_area
    // - math_display
    // - coq
    // - markdown

    // 0. Extract all toplevel blocks.
    // 0.1 Extract the hint and input area blocks.
    const hintBlocks: HintBlock[] = createHintBlocks(inputDocument);
    const inputAreaBlocks: InputAreaBlock[] = createInputBlocks(inputDocument);

    // 0.2 We mask the hint and input area blocks in the input document.
    //     Done to make extraction of coq and math display easier, since 
    //     we don't have to worry about the hint and input area blocks.
    inputDocument = maskInputAndHints(inputDocument, [...hintBlocks, ...inputAreaBlocks]);

    // 0.3 Extract the coq and math display blocks.
    const mathDisplayBlocks = createMathDisplayBlocks(inputDocument);
    const coqBlocks = createCoqBlocks(inputDocument);


    // Create top level prose node.
    
}