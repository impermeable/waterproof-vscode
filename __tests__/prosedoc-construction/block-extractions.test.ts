import { extractCoqBlocks, extractHintBlocks, extractInputBlocks, extractMathDisplayBlocks, extractMathDisplayBlocksCoqDoc } from "../../editor/src/document-construction/block-extraction";
import { typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksMV } from "../../editor/src/document-construction/construct-document";

test("Identify input blocks", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = extractInputBlocks(document);

    expect(blocks.length).toBe(1);
    const [b] = blocks;
    expect(typeguards.isInputAreaBlock(b)).toBe(true);
    expect(b.stringContent).toBe("\n# Test input area\n");
    expect(b.range.from).toBe(10);
    expect(b.range.to).toBe(54);

    expect(b.innerRange.from).toBe(22);
    expect(b.innerRange.to).toBe(41);
});

test("Identity input blocks #2", () => {
    const document = "\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = extractInputBlocks(document);

    expect(blocks.length).toBe(1);
    const [b] = blocks;
    expect(typeguards.isInputAreaBlock(b)).toBe(true);
    expect(b.stringContent).toBe("\n# Test input area\n");
    expect(b.range.from).toBe(1);
    expect(b.range.to).toBe(45);
    expect(b.innerRange.from).toBe(13);
    expect(b.innerRange.to).toBe(32);

});

test("Identify input blocks #3", () => {
    const document = "<input-area>First input area</input-area>\n<input-area>Second input area</input-area>";
    const blocks = extractInputBlocks(document);

    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isInputAreaBlock(b1)).toBe(true);
    expect(typeguards.isInputAreaBlock(b2)).toBe(true);

    expect(b1.stringContent).toBe("First input area");
    expect(b1.range.from).toBe(0);
    expect(b1.range.to).toBe(41);
    expect(b1.innerRange.from).toBe(12);
    expect(b1.innerRange.to).toBe(28);
    
    expect(b2.stringContent).toBe("Second input area");
    expect(b2.range.from).toBe(42);
    expect(b2.range.to).toBe(document.length);
    expect(b2.innerRange.from).toBe(54);
    expect(b2.innerRange.to).toBe(71);
});

test("Identify hint blocks", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const blocks = extractHintBlocks(document);

    expect(blocks.length).toBe(1);
    expect(typeguards.isHintBlock(blocks[0])).toBe(true);
    expect(blocks[0].title).toBe("hint-title-test");
    expect(blocks[0].stringContent).toBe("\n# Test hint\n");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(60);
    expect(blocks[0].innerRange.from).toBe(40);
    expect(blocks[0].innerRange.to).toBe(53);
});

test("Identify hint blocks #2", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint><hint title=\"hint title 2\">Test</hint>";
    const blocks = extractHintBlocks(document);

    expect(blocks.length).toBe(2);

    const [block1, block2] = blocks;

    expect(typeguards.isHintBlock(block1)).toBe(true);
    expect(block1.title).toBe("hint-title-test");
    expect(block1.stringContent).toBe("\n# Test hint\n");
    expect(block1.range.from).toBe(10);
    expect(block1.range.to).toBe(60);
    expect(block1.innerRange.from).toBe(40);
    expect(block1.innerRange.to).toBe(53);

    expect(typeguards.isHintBlock(block2)).toBe(true);
    expect(block2.title).toBe("hint title 2");
    expect(block2.stringContent).toBe("Test");
    expect(block2.range.from).toBe(60);
    expect(block2.range.to).toBe(98);
    expect(block2.innerRange.from).toBe(87);
    expect(block2.innerRange.to).toBe(91);
});

test("Parse Math Display blocks", () => {
    const document = "# Example\n$$ \\frac{1}{2} $$\n";
    const blocks = extractMathDisplayBlocks(document);

    expect(blocks.length).toBe(1);
    expect(typeguards.isMathDisplayBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe(" \\frac{1}{2} ");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(27);
});

test("Parse Math Display blocks #2", () => {
    const document = "# Example\n$$ \\frac{1}{3} $$\n$$ \\frac{1}{2} $$\n";
    const blocks = extractMathDisplayBlocks(document);

    expect(blocks.length).toBe(2);
    expect(typeguards.isMathDisplayBlock(blocks[0])).toBe(true);
    expect(typeguards.isMathDisplayBlock(blocks[1])).toBe(true);
    expect(blocks[0].stringContent).toBe(" \\frac{1}{3} ");
    expect(blocks[1].stringContent).toBe(" \\frac{1}{2} ");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(27);
    expect(blocks[1].range.from).toBe(28);
    expect(blocks[1].range.to).toBe(45);
});

test("Parse Coq blocks #1", () => {
    const document = "# Example\n```coq\nLemma trivial.\n```";
    const blocks = extractCoqBlocks(document);

    expect(blocks.length).toBe(2);
    expect(typeguards.isCodeBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("Lemma trivial.");

    // Outer ranges
    expect(blocks[0].range.from).toBe(9);
    expect(blocks[0].range.to).toBe(document.length);

    // Inner ranges
    expect(blocks[0].innerRange.from).toBe(17);
    expect(blocks[0].innerRange.to).toBe(31);

});

test("Parse Coq blocks #2", () => {
    const document = "```coq\nRequire Import ZArith.\n```\n# Example\n```coq\nLemma trivial.\n```";
    const blocks = extractCoqBlocks(document);

    expect(blocks.length).toBe(2);
    expect(typeguards.isCodeBlock(blocks[0])).toBe(true);
    expect(typeguards.isCodeBlock(blocks[1])).toBe(true);
    expect(blocks[0].stringContent).toBe("Require Import ZArith.");
    expect(blocks[1].stringContent).toBe("Lemma trivial.");

    // Outer ranges first block
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(34);

    // Inner ranges first block
    expect(blocks[0].innerRange.from).toBe(7);
    expect(blocks[0].innerRange.to).toBe(29);

    // Outer ranges second block
    expect(blocks[1].range.from).toBe(43);
    expect(blocks[1].range.to).toBe(document.length);

    // Inner ranges second block
    expect(blocks[1].innerRange.from).toBe(51);
    expect(blocks[1].innerRange.to).toBe(65);
});


test("Parse Coq Blocks #3", () => {
    const content = "```coq\nLemma test\n```";
    const blocks = topLevelBlocksMV(content);

    expect(blocks.length).toBe(1);
    expect(typeguards.isCodeBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("Lemma test");
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(content.length);
    expect(blocks[0].innerRange.from).toBe(7);
    expect(blocks[0].innerRange.to).toBe(content.length - "\n```".length);
});

test("Extract math display from inside coqdoc comment", () => {
    const input = `(** $\\text{math display}$ *)`;
    const blocks = extractMathDisplayBlocksCoqDoc(input);

    // console.log(blocks);

    expect(blocks.length).toBe(1);
    expect(typeguards.isMathDisplayBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("\\text{math display}");
})