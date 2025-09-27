//@ts-nocheck

import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";


export function preambleParser(document: string): WaterproofDocument {
    const blocks: Block[] = [];
    
    const preambleEnd = 96;

    const codeBlock = new CodeBlock(document.slice(0, preambleEnd), {from: 0, to: preambleEnd}, {from: 0, to: preambleEnd});
    const preambleHintBlock = new HintBlock(document.slice(0, preambleEnd), "Preamble Block", {from: 0, to: preambleEnd}, {from: 0, to: preambleEnd}, [codeBlock]);

    blocks.push(preambleHintBlock);

    const codeBlockRest = new CodeBlock(document.slice(preambleEnd), {from : preambleEnd, to: document.length}, {from : preambleEnd, to: document.length});

    blocks.push(codeBlockRest);
    return blocks;
}
