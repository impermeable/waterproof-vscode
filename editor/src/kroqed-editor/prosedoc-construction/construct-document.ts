import { createHintBlocks, createInputBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { HintBlock, InputAreaBlock } from "./blocks/blocktypes";

/**
 * Construct prosemirror document from a string input. 
 * @param inputDocument The input document.
 */
export function createProseDocument(inputDocument: string) {
    // There are five different 'top level' blocks, 
    // - coq
    // - math_display
    // - input_area
    // - hint
    // - markdown

    // 1. Extract the hint and input area blocks.
    const hintBlocks: HintBlock[] = createHintBlocks(inputDocument);
    const inputAreaBlocks: InputAreaBlock[] = createInputBlocks(inputDocument);


    // Create top level prose node.
    
}