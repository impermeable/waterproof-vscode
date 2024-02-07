import { FileFormat } from "../../../../shared";
import { TheSchema } from "../kroqed-schema";
import { extractCoqBlocks, extractHintBlocks, extractInputBlocks, extractBlocksUsingRanges, extractMathDisplayBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { CoqBlock, HintBlock, InputAreaBlock, MarkdownBlock } from "./blocks/blocktypes";
import { root } from "./blocks/schema";
import { extractInterBlockRanges, maskInputAndHints, sortBlocks } from "./utils";
import { Node as ProseNode } from "prosemirror-model";

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
    inputDocument = maskInputAndHints(inputDocument, [...hintBlocks, ...inputAreaBlocks]);

    // 0A.3 Extract the coq and math display blocks.
    const mathDisplayBlocks = extractMathDisplayBlocks(inputDocument);
    const coqBlocks = extractCoqBlocks(inputDocument);

    // 0A.4 Sort the blocks by their range.
    const blocks: Block[] = sortBlocks([...hintBlocks, ...inputAreaBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    const markdownRanges = extractInterBlockRanges(blocks, inputDocument);

    // 0A.5 Extract the markdown blocks based on the ranges.
    const markdownBlocks = extractBlocksUsingRanges<MarkdownBlock>(inputDocument, markdownRanges, MarkdownBlock);
    
    // Note: Blocks parse their own inner blocks.

    // 0A.6 Sort the blocks and return.
    return sortBlocks([...blocks, ...markdownBlocks]);
}

// 0B. Extract the top level blocks from the input document.
export function topLevelBlocksV(inputDocument: string): Block[] {
    // There are two different 'top level' blocks, 
    // - Coqcode
    // - Coqdoc

    // 0B.1 
    const range = { from: 0, to: inputDocument.length };
    return [new CoqBlock(inputDocument, range)];
}



// 1. Construct the prosemirror document from the top level blocks.
export function constructDocument(blocks: Block[]): ProseNode {
    const documentContent: ProseNode[] = blocks.map(block => block.toProseMirror());
    return root(documentContent);
}

// 2. Construct the prosemirror document from the input document.
export function createProseMirrorDocument(input: string, fileFormat: FileFormat): ProseNode {
    let blocks: Block[];

    // 2.1 We differentiate between the two supported file formats
    switch (fileFormat) {
        case FileFormat.MarkdownV:
            blocks = topLevelBlocksMV(input);
            break;
        case FileFormat.RegularV:
            blocks = topLevelBlocksV(input);
            break;
        case FileFormat.Unknown:
            throw new Error("Unknown file format in prosemirror document constructor");
    }

    // 2.2 Construct the document and return
    return constructDocument(blocks);
}