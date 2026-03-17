import { typeguards, constructDocument } from "@impermeable/waterproof-editor";
import { topLevelBlocksLean } from "../../editor/src/document-construction/construct-document";
import { LeanSerializer } from "../../editor/src/leanSerializer";

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
// The ::::multilean / :::: directives produce a ContainerBlock wrapping the
// inner blocks. Blocks inside multilean have their ranges reflecting their true
// positions in the original document string.

test("Empty multilean wrapper produces a ContainerBlock with no inner blocks", () => {
    const document = "\n::::multilean\n\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    expect(cg.innerBlocks.length).toBe(0);
});

test("Multilean wrapper produces a ContainerBlock at top level", () => {
    const document = "\n::::multilean\n# Hello\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    expect(typeguards.isContainerBlock(cg)).toBe(true);
    // The inner block should be the markdown
    const innerMd = cg.innerBlocks.filter(b => typeguards.isMarkdownBlock(b));
    expect(innerMd.length).toBe(1);
    expect(innerMd[0].stringContent).toBe("# Hello");
    expect(innerMd[0].range.from).toBe(15);
    expect(innerMd[0].range.to).toBe(22);
});

test("Multilean ContainerBlock range and innerRange are correct", () => {
    // MultileanOpen "::::multilean\n" starts at 1 (after leading \n), length 14 → {from:1, to:15}
    // MultileanClose "\n::::" at position 22, length 5 → {from:22, to:27}
    // So ContainerBlock range = {from:1, to:27}, innerRange = {from:15, to:22}
    const document = "\n::::multilean\n# Hello\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const cg = blocks.find(b => typeguards.isContainerBlock(b))!;
    expect(cg.range.from).toBe(1);
    expect(cg.range.to).toBe(27);
    expect(cg.innerRange.from).toBe(15);
    expect(cg.innerRange.to).toBe(22);
});

test("Multilean wrapper with a code block", () => {
    // CodeOpen "```lean\n" at 15, inner content at 23, CodeClose "\n```" ends at 37
    // MultileanClose "\n::::" starts at 37
    const document = "\n::::multilean\n```lean\ndef x := 1\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerCode = cg.innerBlocks.filter(b => typeguards.isCodeBlock(b));
    expect(innerCode.length).toBe(1);

    const code = innerCode[0];
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

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerInput = cg.innerBlocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(innerInput.length).toBe(1);

    const input = innerInput[0];
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

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerMath = cg.innerBlocks.filter(b => typeguards.isMathDisplayBlock(b));
    expect(innerMath.length).toBe(1);

    const math = innerMath[0];
    expect(math.stringContent).toBe("\\frac{1}{2}");
    expect(math.range.from).toBe(15);
    expect(math.range.to).toBe(30);
});

test("Multilean wrapper with a hint block", () => {
    const document = '\n::::multilean\n:::hint "title"\nContent\n:::\n::::\n';
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerHint = cg.innerBlocks.filter(b => typeguards.isHintBlock(b));
    expect(innerHint.length).toBe(1);

    const hint = innerHint[0];
    expect(hint.title).toBe("title");
    expect(hint.stringContent).toContain("Content");
    expect(hint.range.from).toBe(15);
});

test("Multilean wrapper with multiple block types", () => {
    // Markdown, a newline separator, and a code block inside multilean
    const document = "\n::::multilean\n## Title\n```lean\ndef x := 1\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerMd = cg.innerBlocks.filter(b => typeguards.isMarkdownBlock(b));
    const innerCode = cg.innerBlocks.filter(b => typeguards.isCodeBlock(b));

    expect(innerMd.length).toBe(1);
    expect(innerCode.length).toBe(1);

    expect(innerMd[0].stringContent).toBe("## Title");
    expect(innerMd[0].range.from).toBe(15);

    expect(innerCode[0].stringContent).toBe("def x := 1");
    // Code block starts after "## Title\n"
    expect(innerCode[0].range.from).toBe(24);
});

test("Multilean wrapper mimicking WaterproofDocument.lean structure", () => {
    // Simplified version of the ATC-003 pattern from WaterproofDocument.lean:
    // multilean containing markdown + code + input + code
    const document =
        "\n::::multilean\n" +
        "## ATC - 003\n" +
        "```lean\nExample\n```\n" +
        ":::input\n```lean\nFix a\n```\n:::\n" +
        "```lean\nQED\n```\n" +
        "::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerMd = cg.innerBlocks.filter(b => typeguards.isMarkdownBlock(b));
    const innerCode = cg.innerBlocks.filter(b => typeguards.isCodeBlock(b));
    const innerInput = cg.innerBlocks.filter(b => typeguards.isInputAreaBlock(b));

    expect(innerMd.length).toBe(1);
    expect(innerMd[0].stringContent).toBe("## ATC - 003");

    expect(innerCode.length).toBe(2);
    expect(innerCode[0].stringContent).toBe("Example");
    expect(innerCode[1].stringContent).toBe("QED");

    expect(innerInput.length).toBe(1);
    expect(innerInput[0].stringContent).toContain("Fix a");

    // All inner block positions should be offset by the multilean open tag
    for (const block of cg.innerBlocks) {
        expect(block.range.from).toBeGreaterThanOrEqual(15);
    }
});

// --- New multilean tests for the typical exercise pattern ---
// The primary multilean use case groups a Lean execution context with an
// input block: code (exercise preamble) + input (student answer) + code (QED).

test("Typical exercise pattern: code + input + code inside multilean", () => {
    const document =
        "\n::::multilean\n" +
        "```lean\nExercise \"ex1\"\nProof:\n```\n" +
        ":::input\n```lean\n  exact h\n```\n:::\n" +
        "```lean\nQED\n```\n" +
        "::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(1);

    const cg = containerBlocks[0];
    const innerCode = cg.innerBlocks.filter(b => typeguards.isCodeBlock(b));
    const innerInput = cg.innerBlocks.filter(b => typeguards.isInputAreaBlock(b));
    const innerNewlines = cg.innerBlocks.filter(b => typeguards.isNewlineBlock(b));

    expect(innerCode.length).toBe(2);
    expect(innerInput.length).toBe(1);
    expect(innerNewlines.length).toBe(2); // between code+input and input+code

    expect(innerCode[0].stringContent).toBe("Exercise \"ex1\"\nProof:");
    expect(innerCode[1].stringContent).toBe("QED");

    // Input area contains an inner code block
    const inputInnerCode = innerInput[0].innerBlocks.filter(b => typeguards.isCodeBlock(b));
    expect(inputInnerCode.length).toBe(1);
    expect(inputInnerCode[0].stringContent).toBe("  exact h");
});

test("Exercise pattern: code before input only (no trailing code block)", () => {
    const document =
        "\n::::multilean\n" +
        "```lean\nExercise \"ex2\"\nProof:\n```\n" +
        ":::input\n```lean\n  trivial\n```\n:::\n" +
        "::::\n";
    const blocks = topLevelBlocksLean(document);

    const cg = blocks.find(b => typeguards.isContainerBlock(b))!;
    expect(typeguards.isContainerBlock(cg)).toBe(true);

    const innerCode = cg.innerBlocks.filter(b => typeguards.isCodeBlock(b));
    const innerInput = cg.innerBlocks.filter(b => typeguards.isInputAreaBlock(b));

    expect(innerCode.length).toBe(1);
    expect(innerInput.length).toBe(1);
    expect(innerCode[0].stringContent).toBe("Exercise \"ex2\"\nProof:");
    expect(innerInput[0].innerBlocks.filter(b => typeguards.isCodeBlock(b))[0].stringContent).toBe("  trivial");
});

test("Two consecutive multilean blocks produce two ContainerBlocks", () => {
    const document =
        "\n::::multilean\n```lean\nblock1\n```\n::::\n" +
        "::::multilean\n```lean\nblock2\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));
    expect(containerBlocks.length).toBe(2);

    const [cg1, cg2] = containerBlocks;
    const code1 = cg1.innerBlocks.filter(b => typeguards.isCodeBlock(b));
    const code2 = cg2.innerBlocks.filter(b => typeguards.isCodeBlock(b));

    expect(code1[0].stringContent).toBe("block1");
    expect(code2[0].stringContent).toBe("block2");
});

test("Content before and after multilean block", () => {
    const document =
        "# Introduction\n" +
        "::::multilean\n" +
        "```lean\nExercise \"ex3\"\nProof:\n```\n" +
        ":::input\n```lean\n  rfl\n```\n:::\n" +
        "```lean\nQED\n```\n" +
        "::::\n" +
        "## Conclusion\n";
    const blocks = topLevelBlocksLean(document);

    const mdBlocks = blocks.filter(b => typeguards.isMarkdownBlock(b));
    const containerBlocks = blocks.filter(b => typeguards.isContainerBlock(b));

    expect(containerBlocks.length).toBe(1);
    expect(mdBlocks.length).toBeGreaterThanOrEqual(1);
    expect(mdBlocks[0].stringContent).toContain("# Introduction");

    const cg = containerBlocks[0];
    expect(cg.innerBlocks.filter(b => typeguards.isCodeBlock(b)).length).toBe(2);
    expect(cg.innerBlocks.filter(b => typeguards.isInputAreaBlock(b)).length).toBe(1);

    // Last block should contain conclusion text
    const lastMd = mdBlocks[mdBlocks.length - 1];
    expect(lastMd.stringContent).toContain("## Conclusion");
});

test("ContainerBlock stringContent matches the inner document slice", () => {
    // stringContent = doc.substring(innerRange.from, innerRange.to)
    const document = "\n::::multilean\n```lean\ndef x := 1\n```\n::::\n";
    const blocks = topLevelBlocksLean(document);

    const cg = blocks.find(b => typeguards.isContainerBlock(b))!;
    // innerRange excludes the ::::multilean\n and \n:::: tags
    expect(cg.stringContent).toBe("```lean\ndef x := 1\n```");
    expect(document.substring(cg.innerRange.from, cg.innerRange.to)).toBe(cg.stringContent);
});

test("Serialization round-trip of typical exercise pattern is identity", () => {
    const document =
        "\n::::multilean\n" +
        "```lean\nExercise \"ex\"\nProof:\n```\n" +
        ":::input\n```lean\n  exact h\n```\n:::\n" +
        "```lean\nQED\n```\n" +
        "::::\n";
    const blocks = topLevelBlocksLean(document);
    const doc = constructDocument(blocks);
    const out = new LeanSerializer().serializeDocument(doc);
    expect(out).toBe(document);
});
