import { Block, FileFormat, HintBlock, InputAreaBlock, MarkdownBlock, typeguards, utils } from "@impermeable/waterproof-editor";
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
    // const blocks = [...hintBlocks, ...inputAreaBlocks];
    // const coqBlockRanges = extractInterBlockRanges(blocks, inputDocument);
    
    // Extract the coq blocks based on the ranges.
    // const coqBlocks = coqBlockRanges.map(range => {
    //     const content = inputDocument.slice(range.from, range.to);
    //     return new CodeBlock(content, "", "", "", "", range);
    // });

    const sortedBlocks = utils.sortBlocks([...hintBlocks, ...inputAreaBlocks]); // , ...coqBlocks]);
    const prunedBlocks = sortedBlocks.filter(block => {
        if (typeguards.isCodeBlock(block) && (block.stringContent === "\n")) return false;

        return true;
    });
    return prunedBlocks;
}
