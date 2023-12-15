import { sortBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/block-helpers";
import { createHintBlocks, createInputBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/block-parsing";
import { isCoqBlock, isHintBlock, isInputAreaBlock, isMarkdownBlock, isMathDisplayBlock } from "../../editor/src/kroqed-editor/new-translator-parser/blocks";
import { constructBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/document-constructor";

test("Parse then sort input areas and hint blocks #1", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const hintBlocks = createHintBlocks(document);
    const inputAreaBlocks = createInputBlocks(document);

    const sorted = sortBlocks([ ...hintBlocks, ...inputAreaBlocks ]);
    expect(sorted.length).toBe(2);
    expect(isInputAreaBlock(sorted[0])).toBe(true);
    expect(isHintBlock(sorted[1])).toBe(true);
}); 

test("Parse then sort input areas and hint blocks #2", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n<input-area>\n# Test input area\n</input-area>\n";
    const hintBlocks = createHintBlocks(document);
    const inputAreaBlocks = createInputBlocks(document);

    const sorted = sortBlocks([ ...hintBlocks, ...inputAreaBlocks ]);
    expect(sorted.length).toBe(2);
    expect(isHintBlock(sorted[0])).toBe(true);
    expect(isInputAreaBlock(sorted[1])).toBe(true);
}); 

test("Parse all root level blocks", () => {
    const blocks = constructBlocks("<input-area>\n# Example\n</input-area>\n$$ \\frac{1}{3} $$\n$$ \\frac{1}{2} $$\n```coq\nLemma trivial.\n```");
    expect(blocks.length).toBe(7);

    expect(isInputAreaBlock(blocks[0])).toBe(true);
    expect(isMarkdownBlock(blocks[1])).toBe(true);
    expect(isMathDisplayBlock(blocks[2])).toBe(true);
    expect(isMarkdownBlock(blocks[3])).toBe(true);
    expect(isMathDisplayBlock(blocks[4])).toBe(true);
    expect(isMarkdownBlock(blocks[5])).toBe(true);
    expect(isCoqBlock(blocks[6])).toBe(true);

    expect(blocks[0].content).toBe("# Example");
    expect(blocks[1].content).toBe("\n");
    expect(blocks[2].content).toBe(" \\frac{1}{3} ");
    expect(blocks[3].content).toBe("\n");
    expect(blocks[4].content).toBe(" \\frac{1}{2} ");
    expect(blocks[5].content).toBe("\n");
    expect(blocks[6].content).toBe("Lemma trivial.");
});

test("parse a coq block", () => {
    const blocks = constructBlocks("Lemma trivial.");
    
});

test("PARSE", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n$$ \\frac{1}{3} $$\n$$ \\frac{1}{2} $$\n```coq\nLemma trivial.\n```";
    const blocks = constructBlocks(document);
    console.log(blocks.map((block) => block.toProseMirror().toJSON()));
});