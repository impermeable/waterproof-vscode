import { sortBlocks } from "./block-helpers";
import { createHintBlocks, createInputBlocks, createMathDisplayBlocks, createCoqBlocks, createMarkdownBlocks } from "./block-parsing";
import { Block } from "./blocks";
import { extractInterBlockRanges } from "./utils";

export function constructBlocks(inputDocument: string, skipHintAndInput: boolean = false) {
    let hintBlocks: Block[] = [];
    let inputAreaBlocks: Block[] = [];
    if (!skipHintAndInput) {
        hintBlocks = createHintBlocks(inputDocument);
        inputAreaBlocks = createInputBlocks(inputDocument);
    } else {
        hintBlocks = [];
        inputAreaBlocks = [];
    }

    // We have the input and hint blocks at this point. 
    // Find the math_diplays and coq code blocks.
    const mathDisplayBlocks = createMathDisplayBlocks(inputDocument);
    const coqBlocks = createCoqBlocks(inputDocument);

    // Sort the blocks
    const sortedBlocks = sortBlocks([...inputAreaBlocks, ...hintBlocks, ...mathDisplayBlocks, ...coqBlocks]);
    
    const ranges = extractInterBlockRanges(sortedBlocks, inputDocument);

    const markdownBlocks = createMarkdownBlocks(inputDocument, ranges);
    const allBlocks = sortBlocks([...sortedBlocks, ...markdownBlocks]);
    return allBlocks;
}