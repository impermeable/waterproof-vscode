import { text } from "../../editor/src/kroqed-editor/translation/prosemirror-document-helpers";
import { BLOCK_NAME, createCoqBlocks, createMathDisplayBlocks, hintAndInputBlocks, isCoqBlock, isHintBlock, isInputAreaBlock, isMathDisplayBlock, sortBlocks, testingTest } from "../../editor/src/kroqed-editor/translation/testingTest";

test("Identify input and hint blocks", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const blocks = hintAndInputBlocks(document);

    expect(blocks.hintBlocks.length).toBe(1);
    expect(blocks.inputAreaBlocks.length).toBe(1);

    expect(blocks.hintBlocks[0].title).toBe("hint-title-test");
    expect(blocks.hintBlocks[0].content).toBe("# Test hint");

    expect(blocks.inputAreaBlocks[0].content).toBe("# Test input area");

    expect(blocks.hintBlocks[0].range.from).toBe(55);
    expect(blocks.hintBlocks[0].range.to).toBe(105);

    expect(blocks.inputAreaBlocks[0].range.from).toBe(10);
    expect(blocks.inputAreaBlocks[0].range.to).toBe(54);
});

test("Sort blocks #1", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 1, to: 2}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].name).toBe("first");
    expect(sorted[1].name).toBe("second");
});

test("Sort blocks #2", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 1, to: 2}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror},
        {name: "third", range: {from: 2, to: 3}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(3);
    expect(sorted[0].name).toBe("first");
    expect(sorted[1].name).toBe("second");
    expect(sorted[2].name).toBe("third");
});

// TODO: What is the expected behaviour in this case?
test("Sort blocks with same range", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 0, to: 1}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].name).toBe("second");
    expect(sorted[1].name).toBe("first");
});

test("Parse then sort input areas and hint blocks #1", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const blocks = hintAndInputBlocks(document);

    const sorted = sortBlocks([ ...blocks.hintBlocks, ...blocks.inputAreaBlocks ]);
    expect(sorted.length).toBe(2);
    expect(isInputAreaBlock(sorted[0])).toBe(true);
    expect(isHintBlock(sorted[1])).toBe(true);
}); 

test("Parse then sort input areas and hint blocks #2", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = hintAndInputBlocks(document);

    const sorted = sortBlocks([ ...blocks.hintBlocks, ...blocks.inputAreaBlocks ]);
    expect(sorted.length).toBe(2);
    expect(isHintBlock(sorted[0])).toBe(true);
    expect(isInputAreaBlock(sorted[1])).toBe(true);
}); 

test("Parse Math Display blocks", () => {
    const document = "# Example\n$$ \\frac{1}{2} $$\n";
    const blocks = createMathDisplayBlocks(document);

    expect(blocks.length).toBe(1);
    expect(isMathDisplayBlock(blocks[0])).toBe(true);
    expect(blocks[0].content).toBe(" \\frac{1}{2} ");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(27);
});

test("Parse Math Display blocks #2", () => {
    const document = "# Example\n$$ \\frac{1}{3} $$\n$$ \\frac{1}{2} $$\n";
    const blocks = createMathDisplayBlocks(document);

    expect(blocks.length).toBe(2);
    expect(isMathDisplayBlock(blocks[0])).toBe(true);
    expect(isMathDisplayBlock(blocks[1])).toBe(true);
    expect(blocks[0].content).toBe(" \\frac{1}{3} ");
    expect(blocks[1].content).toBe(" \\frac{1}{2} ");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(27);
    expect(blocks[1].range.from).toBe(28);
    expect(blocks[1].range.to).toBe(45);

    const expectedOutput0 = {"content": [{"text": " \\frac{1}{3} ", "type": "text"}], "type": "math_display"};
    const expectedOutput1 = {"content": [{"text": " \\frac{1}{2} ", "type": "text"}], "type": "math_display"};
    const out0 = blocks[0].toProseMirror().toJSON();
    const out1 = blocks[1].toProseMirror().toJSON();
    expect(out0).toEqual(expectedOutput0);
    expect(out1).toEqual(expectedOutput1);
});

test("Parse Coq blocks", () => {
    const document = "# Example\n```coq\nLemma trivial.\n```";
    const blocks = createCoqBlocks(document);

    expect(blocks.length).toBe(1);
    expect(isCoqBlock(blocks[0])).toBe(true);
    expect(blocks[0].content).toBe("Lemma trivial.");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(35);
});

test("big boii", () => {
    testingTest("# Example\n$$ \\frac{1}{3} $$\n$$ \\frac{1}{2} $$\n```coq\nLemma trivial.\n```");
});