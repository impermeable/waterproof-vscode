import { typeguards } from "waterproof-editor";
import { extractCoqBlocks, extractCoqDoc, extractHintBlocks, extractInputBlocks, extractMathDisplayBlocks, extractMathDisplayBlocksCoqDoc } from "../../editor/src/document-construction/block-extraction";

test("Identify input blocks", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = extractInputBlocks(document);

    expect(blocks.length).toBe(1);
    expect(typeguards.isInputAreaBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("\n# Test input area\n");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(54);
});

test("Identity input blocks #2", () => {
    const document = "\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = extractInputBlocks(document);

    expect(blocks.length).toBe(1);
    expect(typeguards.isInputAreaBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("\n# Test input area\n");
    expect(blocks[0].range.from).toBe(1);
    expect(blocks[0].range.to).toBe(45);
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

    expect(blocks.length).toBe(1);
    expect(typeguards.isCoqBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("Lemma trivial.");
    expect(blocks[0].range.from).toBe(9);
    expect(blocks[0].range.to).toBe(35);
});

test("Parse Coq blocks #2", () => {
    const document = "```coq\nRequire Import ZArith.\n```\n# Example\n```coq\nLemma trivial.\n```";
    const blocks = extractCoqBlocks(document);

    expect(blocks.length).toBe(2);
    expect(typeguards.isCoqBlock(blocks[0])).toBe(true);
    expect(typeguards.isCoqBlock(blocks[1])).toBe(true);
    expect(blocks[0].stringContent).toBe("Require Import ZArith.");
    expect(blocks[1].stringContent).toBe("Lemma trivial.");
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(34);

    expect(blocks[1].range.from).toBe(43);
    expect(blocks[1].range.to).toBe(69);
});

test("Extract coqdoc blocks", () => {
    const input = `(** * Header in coqdoc comment *)\nCoq code\n(** $\\text{math display}$ *)\nMore Coq code\n`;
    const blocks = extractCoqDoc(input);

    // console.log(blocks);

    expect(blocks.length).toBe(2);
    expect(typeguards.isCoqDocBlock(blocks[0])).toBe(true);
    expect(typeguards.isCoqDocBlock(blocks[1])).toBe(true);

    expect(blocks[0].stringContent).toBe("* Header in coqdoc comment ");
    expect(blocks[1].stringContent).toBe("$\\text{math display}$ ");
});

test("Extract math display from inside coqdoc comment", () => {
    const input = `(** $\\text{math display}$ *)`;
    const blocks = extractMathDisplayBlocksCoqDoc(input);

    // console.log(blocks);

    expect(blocks.length).toBe(1);
    expect(typeguards.isMathDisplayBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("\\text{math display}");
})