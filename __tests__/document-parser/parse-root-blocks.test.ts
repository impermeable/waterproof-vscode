import { createCoqBlocks, createHintBlocks, createInputBlocks, createMarkdownBlocks, createMathDisplayBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/block-parsing";
import { isCoqBlock, isMathDisplayBlock } from "../../editor/src/kroqed-editor/new-translator-parser/blocks";
import { createCoqDoc } from "../../editor/src/kroqed-editor/new-translator-parser/inner-block-logic/coq-block";

test("Identify input blocks", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = createInputBlocks(document);

    expect(blocks.length).toBe(1);
    expect(blocks[0].content).toBe("# Test input area");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(54);
});

test("Identify hint blocks", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const blocks = createHintBlocks(document);

    expect(blocks.length).toBe(1);
    expect(blocks[0].title).toBe("hint-title-test");
    expect(blocks[0].content).toBe("# Test hint");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(60);
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

test("Markdown blocks from ranges #1" , () => {
    const document = "# Example\n```coq\nLemma trivial.\n```";
    const markdownBlocks = createMarkdownBlocks(document, [
        { from: 0, to: 10 }
    ]);
    expect(markdownBlocks.length).toBe(1);
    expect(markdownBlocks[0].content).toBe("# Example\n");
});

test("Markdown blocks from ranges #2" , () => {
    const document = "# Title 1\n```coq\nLemma trivial.\n```\n# Title 2";
    const markdownBlocks = createMarkdownBlocks(document, [
        { from: 0,  to: 10 },
        { from: 36, to: 45 }
    ]);
    expect(markdownBlocks.length).toBe(2);
    expect(markdownBlocks[0].content).toBe("# Title 1\n");
    expect(markdownBlocks[1].content).toBe("# Title 2");
});

test("Parse coqdoc comment", () => {
    // TODO: We should probably remove the \n at the start and the end of the coqdown blocks, but I do not
    // know whether that messes with the textdocmapping.
    const comment = "* Test\n$\\text{math display}$\n %\\text{math inline}%";
    const blocks = createCoqDoc(comment);
    // console.log(blocks);
});