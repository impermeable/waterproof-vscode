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

// --- Multilean directive tests ---
// The ::::multilean / :::: directives should be skipped (no blocks produced),
// but all blocks inside should have their ranges reflect their true positions
// in the original document string.
// TODO: Update these tests when multilean becomes editable.

test("Empty multilean wrapper produces no content blocks", () => {
    const document = "\n::::multilean\n\n::::\n";
    const blocks = topLevelBlocksLean(document);
    // The multilean open/close markers should be skipped entirely
    expect(blocks.length).toBe(0);
});

test("Multilean wrapper with markdown content", () => {
    // "\n::::multilean\n" occupies positions 0–14, so "# Hello" starts at 15
    const document = "\n::::multilean\n# Hello\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const mdBlocks = blocks.filter(b => typeguards.isMarkdownBlock(b));
    expect(mdBlocks.length).toBe(1);
    expect(mdBlocks[0].stringContent).toBe("# Hello");
    expect(mdBlocks[0].range.from).toBe(15);
    expect(mdBlocks[0].range.to).toBe(22);
});

test("Multilean wrapper with a code block", () => {
    // MultileanOpen "::::multilean\n" at 1–15
    // CodeOpen "```lean\n" at 15–23, inner content at 23–33, CodeClose "\n```" at 33–37
    const document = "\n::::multilean\n```lean\ndef x := 1\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));
    expect(codeBlocks.length).toBe(1);

    const code = codeBlocks[0];
    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(code.stringContent).toBe("def x := 1");
    expect(code.range.from).toBe(15);
    expect(code.range.to).toBe(37);
    expect(code.innerRange.from).toBe(23);
    expect(code.innerRange.to).toBe(33);
});

test("Multilean wrapper with an input area", () => {
    // MultileanOpen at 1–15, InputOpen ":::input\n" at 15–24
    // Inner content "# Help" at 24–30, Close "\n:::" at 30–34
    const document = "\n::::multilean\n:::input\n# Help\n:::\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(1);

    const input = inputBlocks[0];
    expect(typeguards.isInputAreaBlock(input)).toBe(true);
    expect(input.stringContent).toContain("# Help");
    expect(input.range.from).toBe(15);
    expect(input.range.to).toBe(34);
    expect(input.innerRange.from).toBe(24);
    expect(input.innerRange.to).toBe(30);
});

test("Multilean wrapper with a math display block", () => {
    // MultileanOpen at 1–15, MathDisplay "$$`\\frac{1}{2}`" at 15–30
    const document = "\n::::multilean\n$$`\\frac{1}{2}`\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const mathBlocks = blocks.filter(b => typeguards.isMathDisplayBlock(b));
    expect(mathBlocks.length).toBe(1);

    const math = mathBlocks[0];
    expect(typeguards.isMathDisplayBlock(math)).toBe(true);
    expect(math.stringContent).toBe("\\frac{1}{2}");
    expect(math.range.from).toBe(15);
    expect(math.range.to).toBe(30);
});

test("Multilean wrapper with a hint block", () => {
    // MultileanOpen at 1–15, HintOpen at 15–30, content 30–38, Close 38–42
    const document = '\n::::multilean\n:::hint "title"\nContent\n:::\n::::\n';
    const blocks = topLevelBlocksLean(document);

    const hintBlocks = blocks.filter(b => typeguards.isHintBlock(b));
    expect(hintBlocks.length).toBe(1);

    const hint = hintBlocks[0];
    expect(typeguards.isHintBlock(hint)).toBe(true);
    expect(hint.title).toBe("title");
    expect(hint.stringContent).toContain("Content");
    expect(hint.range.from).toBe(15);
    expect(hint.range.to).toBe(42);
});

test("Multilean wrapper with multiple block types", () => {
    // Markdown, a newline separator, and a code block inside multilean
    const document = "\n::::multilean\n## Title\n```lean\ndef x := 1\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const mdBlocks = blocks.filter(b => typeguards.isMarkdownBlock(b));
    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));

    expect(mdBlocks.length).toBe(1);
    expect(codeBlocks.length).toBe(1);

    expect(mdBlocks[0].stringContent).toBe("## Title");
    expect(mdBlocks[0].range.from).toBe(15);

    expect(codeBlocks[0].stringContent).toBe("def x := 1");
    // Code block starts after "## Title\n"
    expect(codeBlocks[0].range.from).toBe(24);
});

test("Multilean wrapper mimicking WaterproofDocument.lean structure", () => {
    // Simplified version of the ATC-003 pattern from WaterproofDocument.lean:
    // preamble-like text, then multilean containing markdown + code + input + code
    const document =
        "\n::::multilean\n" +
        "## ATC - 003\n" +
        "```lean\nExample\n```\n" +
        ":::input\n```lean\nFix a\n```\n:::\n" +
        "```lean\nQED\n```\n" +
        "::::\n";
    const blocks = topLevelBlocksLean(document);

    const mdBlocks = blocks.filter(b => typeguards.isMarkdownBlock(b));
    const codeBlocks = blocks.filter(b => typeguards.isCodeBlock(b));
    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));

    expect(mdBlocks.length).toBe(1);
    expect(mdBlocks[0].stringContent).toBe("## ATC - 003");

    expect(codeBlocks.length).toBe(2);
    expect(codeBlocks[0].stringContent).toBe("Example");
    expect(codeBlocks[1].stringContent).toBe("QED");

    expect(inputBlocks.length).toBe(1);
    expect(inputBlocks[0].stringContent).toContain("Fix a");

    // All block positions should be offset by the multilean open tag
    for (const block of blocks) {
        expect(block.range.from).toBeGreaterThanOrEqual(15);
    }
});
