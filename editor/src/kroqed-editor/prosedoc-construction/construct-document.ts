import { FileFormat } from "../../../../shared";
import { extractCoqBlocks, extractHintBlocks, extractInputBlocks, extractBlocksUsingRanges, extractMathDisplayBlocks } from "./block-extraction";
import { Block } from "./blocks";
import { CoqBlock, HintBlock, InputAreaBlock, MarkdownBlock } from "./blocks/blocktypes";
import { root } from "./blocks/schema";
import { isCoqBlock } from "./blocks/typeguards";
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

    // 0A.6 Prune empty blocks.
    const allBlocks = sortBlocks([...blocks, ...markdownBlocks]);

    // 0A.6 Sort the blocks and return.
    return allBlocks;
}

// 0B. Extract the top level blocks from the input document.
export function topLevelBlocksV(inputDocument: string): Block[] {
    // There are three different 'top level' blocks, 
    // - Hint
    // - InputArea
    // - Coq

    // We should also allow input and hints as we do with v files.
    // The syntax is 
    // (* begin hint : [hint description] *) and (* end hint *)
    // (* begin input *) and (* end input *)

    const hintBlocks = extractHintBlocks(inputDocument, FileFormat.RegularV);
    const inputAreaBlocks = extractInputBlocks(inputDocument, FileFormat.RegularV);
    const blocks = [...hintBlocks, ...inputAreaBlocks];
    const coqBlockRanges = extractInterBlockRanges(blocks, inputDocument);
    
    // Extract the coq blocks based on the ranges.
    const coqBlocks = coqBlockRanges.map(range => {
        const content = inputDocument.slice(range.from, range.to);
        return new CoqBlock(content, "", "", "", "", range);
    });

    const sortedBlocks = sortBlocks([...hintBlocks, ...inputAreaBlocks, ...coqBlocks]);
    const prunedBlocks = sortedBlocks.filter(block => {
        if (isCoqBlock(block) && (block.stringContent === "\n")) return false;

        return true;
    });
    return prunedBlocks;
}



// 1. Construct the prosemirror document from the top level blocks.
export function constructDocument(blocks: Block[]): ProseNode {
    console.log("BLOKCS")
    console.log(blocks)
    const documentContent: ProseNode[] = blocks.map(block => block.toProseMirror());
    return root(documentContent);
}

// 2. Construct the prosemirror document from the input document.
export function createProseMirrorDocument(input: string, fileFormat: FileFormat): [ProseNode, Block[]] {
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

    let document = constructDocument(blocks)
    // 2.2 Construct the document and return
    return [document, blocks];
}