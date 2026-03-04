import { BlockRange, typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksLean } from "../../editor/src/document-construction/construct-document";

/**
 * Lean equivalents of the block extraction tests in block-extractions.test.ts.
 * Since Lean does not have separate extraction functions like extractInputBlocks,
 * extractHintBlocks, etc., we use topLevelBlocksLean and filter by block type.
 */

// --- Input block tests (equivalents of "Identify input blocks" #1, #2, #3) ---

test("Identify input blocks (Lean)", () => {
    // Lean equivalent of "Identify input blocks" (Coq)
    const document = "# Example\n:::input\n# Test input area\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(1);

    const [b] = inputBlocks;
    expect(typeguards.isInputAreaBlock(b)).toBe(true);
    expect(b.stringContent).toBe("# Test input area");
    expect(b.range.from).toBe(10);
    expect(b.range.to).toBe(40);
    expect(b.innerRange.from).toBe(19);
    expect(b.innerRange.to).toBe(36);
});

test("Identify input blocks (Lean) #2", () => {
    // Lean equivalent of "Identity input blocks #2" (Coq)
    const document = "\n:::input\n# Test input area\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(1);

    const [b] = inputBlocks;
    expect(typeguards.isInputAreaBlock(b)).toBe(true);
    expect(b.stringContent).toBe("# Test input area");
    expect(b.range.from).toBe(1);
    expect(b.range.to).toBe(31);
    expect(b.innerRange.from).toBe(10);
    expect(b.innerRange.to).toBe(27);
});

test("Identify input blocks (Lean) #3", () => {
    // Lean equivalent of "Identify input blocks #3" (Coq, two consecutive input areas)
    const document = "\n:::input\nFirst\n:::\n:::input\nSecond\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(2);

    const [b1, b2] = inputBlocks;
    expect(typeguards.isInputAreaBlock(b1)).toBe(true);
    expect(typeguards.isInputAreaBlock(b2)).toBe(true);

    expect(b1.stringContent).toBe("First");
    expect(b2.stringContent).toBe("Second");
});

// --- Hint block tests (equivalents of "Identify hint blocks" #1, #2) ---

test("Identify hint blocks (Lean)", () => {
    // Lean equivalent of "Identify hint blocks" (Coq)
    const document = "# Example\n:::hint \"hint-title-test\"\n# Test hint\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const hintBlocks = blocks.filter(b => typeguards.isHintBlock(b));
    expect(hintBlocks.length).toBe(1);

    expect(typeguards.isHintBlock(hintBlocks[0])).toBe(true);
    expect(hintBlocks[0].title).toBe("hint-title-test");
    expect(hintBlocks[0].stringContent).toContain("# Test hint");
});

test("Identify hint blocks (Lean) #2", () => {
    // Lean equivalent of "Identify hint blocks #2" (Coq, two consecutive hints)
    const document = "# Example\n:::hint \"hint-title-test\"\n# Test hint\n:::\n:::hint \"hint title 2\"\nTest\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const hintBlocks = blocks.filter(b => typeguards.isHintBlock(b));
    expect(hintBlocks.length).toBe(2);

    const [block1, block2] = hintBlocks;

    expect(typeguards.isHintBlock(block1)).toBe(true);
    expect(block1.title).toBe("hint-title-test");
    expect(block1.stringContent).toContain("# Test hint");

    expect(typeguards.isHintBlock(block2)).toBe(true);
    expect(block2.title).toBe("hint title 2");
    expect(block2.stringContent).toContain("Test");
});

// --- Math display block tests (equivalents of "Parse Math Display blocks" #1, #2) ---

test("Parse Math Display blocks (Lean)", () => {
    // Lean equivalent of "Parse Math Display blocks" (Coq)
    // Lean uses $$`...` instead of $$...$$
    const document = "# Example\n$$`\\frac{1}{2}`\n";
    const blocks = topLevelBlocksLean(document);

    const mathBlocks = blocks.filter(b => typeguards.isMathDisplayBlock(b));
    expect(mathBlocks.length).toBe(1);
    expect(typeguards.isMathDisplayBlock(mathBlocks[0])).toBe(true);
    expect(mathBlocks[0].stringContent).toBe("\\frac{1}{2}");
});

test("Parse Math Display blocks (Lean) #2", () => {
    // Lean equivalent of "Parse Math Display blocks #2" (Coq)
    const document = "# Example\n$$`\\frac{1}{3}`\n$$`\\frac{1}{2}`\n";
    const blocks = topLevelBlocksLean(document);

    const mathBlocks = blocks.filter(b => typeguards.isMathDisplayBlock(b));
    expect(mathBlocks.length).toBe(2);
    expect(typeguards.isMathDisplayBlock(mathBlocks[0])).toBe(true);
    expect(typeguards.isMathDisplayBlock(mathBlocks[1])).toBe(true);
    expect(mathBlocks[0].stringContent).toBe("\\frac{1}{3}");
    expect(mathBlocks[1].stringContent).toBe("\\frac{1}{2}");
});

// --- Code block tests (equivalents of "Parse Coq blocks" #1, #2, #3) ---

test("Parse Lean code blocks #1", () => {
    // Lean equivalent of "Parse Coq blocks #1" (Coq)
    const document = "# Example\n```lean\ndef test := 42\n```";
    const blocks = topLevelBlocksLean(document);

    // Lean code blocks require a preceding newline token; we expect md, newline, code
    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));
    expect(codeBlocks.length).toBe(1);

    const [code] = codeBlocks;
    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(code.stringContent).toBe("def test := 42");

    // Outer ranges: from ```lean\n to \n```
    expect(code.range.from).toBe(10);
    expect(code.range.to).toBe(document.length);

    // Inner ranges: content within code fences
    expect(code.innerRange.from).toBe(18);
    expect(code.innerRange.to).toBe(32);
});

test("Parse Lean code blocks #2", () => {
    // Lean equivalent of "Parse Coq blocks #2" (Coq, two code blocks)
    const document = "\n```lean\nimport Mathlib\n```\n# Example\n```lean\ndef trivial := true\n```";
    const blocks = topLevelBlocksLean(document);

    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));
    expect(codeBlocks.length).toBe(2);

    const [code1, code2] = codeBlocks;
    expect(typeguards.isCodeBlock(code1)).toBe(true);
    expect(typeguards.isCodeBlock(code2)).toBe(true);
    expect(code1.stringContent).toBe("import Mathlib");
    expect(code2.stringContent).toBe("def trivial := true");

    // Outer ranges first block
    expect(code1.range.from).toBe(1);
    expect(code1.range.to).toBe(27);

    // Inner ranges first block
    expect(code1.innerRange.from).toBe(9);
    expect(code1.innerRange.to).toBe(23);

    // Outer ranges second block
    expect(code2.range.from).toBe(38);
    expect(code2.range.to).toBe(document.length);

    // Inner ranges second block
    expect(code2.innerRange.from).toBe(46);
    expect(code2.innerRange.to).toBe(65);
});

test("Parse Lean code blocks #3", () => {
    // Lean equivalent of "Parse Coq Blocks #3" (Coq, single code block via topLevel)
    const content = "\n```lean\ndef test := 42\n```";
    const blocks = topLevelBlocksLean(content);

    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));
    expect(codeBlocks.length).toBe(1);
    expect(typeguards.isCodeBlock(codeBlocks[0])).toBe(true);
    expect(codeBlocks[0].stringContent).toBe("def test := 42");
    expect(codeBlocks[0].range.from).toBe(1);
    expect(codeBlocks[0].range.to).toBe(content.length);
    expect(codeBlocks[0].innerRange.from).toBe(9);
    expect(codeBlocks[0].innerRange.to).toBe(content.length - "\n```".length);
});

// --- Failing test demonstrating parser bug ---

test("Lean parser extracts hint titles", () => {
    // Regression test for a bug in editor/src/document-construction/lean.ts
    // where the hint title was read from the wrong capture group index.
    // See also: "Identify hint blocks (Lean)" tests above.

    const document = '# Example\n:::hint "my title"\nSome content\n:::\n';
    const blocks = topLevelBlocksLean(document);

    const hintBlocks = blocks.filter(b => typeguards.isHintBlock(b));
    expect(hintBlocks.length).toBe(1);

    expect(hintBlocks[0].title).toBe("my title");
});
