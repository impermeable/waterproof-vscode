import { TheSchema } from "../kroqed-schema";
import { extractCoqBlocks, extractHintBlocks, extractInputBlocks, extractBlocksUsingRanges, extractMathDisplayBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { HintBlock, InputAreaBlock, MarkdownBlock } from "./blocks/blocktypes";
import { root } from "./blocks/schema";
import { extractInterBlockRanges, maskInputAndHints, sortBlocks } from "./utils";
import { Node as ProseNode } from "prosemirror-model";

// 0. Extract the top level blocks from the input document.
export function topLevelBlocks(inputDocument: string) {
    // There are five different 'top level' blocks, 
    // - hint
    // - input_area
    // - math_display
    // - coq
    // - markdown

    // 0.1 Extract the hint and input area blocks.
    const hintBlocks: HintBlock[] = extractHintBlocks(inputDocument);
    const inputAreaBlocks: InputAreaBlock[] = extractInputBlocks(inputDocument);

    // 0.2 Mask the hint and input area blocks in the input document.
    //     Done to make extraction of coq and math display easier, since 
    //     we don't have to worry about the hint and input area blocks.
    inputDocument = maskInputAndHints(inputDocument, [...hintBlocks, ...inputAreaBlocks]);

    // 0.3 Extract the coq and math display blocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(inputDocument);
    const coqBlocks = extractCoqBlocks(inputDocument);

    // 0.4 Sort the blocks by their range.
    const blocks: Block[] = sortBlocks([...hintBlocks, ...inputAreaBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    const markdownRanges = extractInterBlockRanges(blocks, inputDocument);

    // 0.5 Extract the markdown blocks based on the ranges.
    const markdownBlocks = extractBlocksUsingRanges<MarkdownBlock>(inputDocument, markdownRanges, MarkdownBlock);
    
    // Note: Blocks parse their own inner blocks.

    // 0.6 Sort the blocks and return.
    return sortBlocks([...blocks, ...markdownBlocks]);
}

// 1. Construct the prosemirror document from the top level blocks.
export function constructDocument(blocks: Block[]): ProseNode {
    const documentContent: ProseNode[] = blocks.map(block => block.toProseMirror());
    return root(documentContent);
}

// 2. Construct the prosemirror document from the input document.
export function createProseMirrorDocument(input: string): ProseNode {
    const blocks = topLevelBlocks(input);
    return constructDocument(blocks);
}