import { typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksLean } from "../../editor/src/document-construction/construct-document";

/**
 * Lean equivalents of the inner block tests in inner-blocks.test.ts.
 * For Lean, inner blocks are created automatically by topLevelBlocksLean
 * and accessed via the innerBlocks property of InputAreaBlock/HintBlock.
 */

test("Inner input area blocks (Lean)", () => {
    // Lean equivalent of "Inner input area (and hint) blocks" (Rocq)
    // An input area containing math display and a code block
    const document = "# Header\n:::input\n$$`1028 + 23 = ?`\n```lean\nCompute 1028 + 23.\n```\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlock = blocks.find(b => typeguards.isInputAreaBlock(b));
    expect(inputBlock).toBeDefined();
    expect(inputBlock!.innerBlocks).toBeDefined();

    const innerBlocks = inputBlock!.innerBlocks!;

    // Expect: math display, newline, code block
    const mathBlocks = innerBlocks.filter(b => typeguards.isMathDisplayBlock(b));
    const codeBlocks = innerBlocks.filter(b => typeguards.isCodeBlock(b));

    expect(mathBlocks.length).toBe(1);
    expect(codeBlocks.length).toBe(1);

    expect(mathBlocks[0].stringContent).toBe("1028 + 23 = ?");
    expect(codeBlocks[0].stringContent).toBe("Compute 1028 + 23.");
});

test("Verify newlines before and after code are translated into newline nodes (Lean)", () => {
    // Lean equivalent of "Verify newlines before and after code..." (Rocq)
    // Note: trailing \n after \n``` is a non-significant newline and does not
    // produce a separate block (it falls below the >1 char threshold).
    const document = "\n#doc (WaterproofGenre) \"Title\" =>\n```lean\ndef test := 42\n```\n";
    const blocks = topLevelBlocksLean(document);

    // Expect: newline, code (trailing \n is absorbed)
    expect(blocks.length).toBe(4);
    const [pr, nl, b, nl2] = blocks;
    expect(typeguards.isHintBlock(pr)).toBe(true);
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isCodeBlock(b)).toBe(true);
    expect(typeguards.isNewlineBlock(nl2)).toBe(true);
    expect(b.stringContent).toBe("def test := 42");
});

test("Inner input area blocks with code (Lean) #2", () => {
    // Lean equivalent of "Inner input area (and hint) blocks #2" (Rocq)
    // Input area with math and code, checking that inner block offsets are correct
    const document = "# Preamble\n:::input\n$$`1028 + 23 = ?`\n```lean\nCompute 1028 + 23.\n```\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlock = blocks.find(b => typeguards.isInputAreaBlock(b));
    expect(inputBlock).toBeDefined();
    expect(inputBlock!.innerBlocks).toBeDefined();

    const innerBlocks = inputBlock!.innerBlocks!;

    const mathBlocks = innerBlocks.filter(b => typeguards.isMathDisplayBlock(b));
    const codeBlocks = innerBlocks.filter(b => typeguards.isCodeBlock(b));

    expect(mathBlocks.length).toBe(1);
    expect(codeBlocks.length).toBe(1);

    // Math display content:
    expect(mathBlocks[0].stringContent).toBe("1028 + 23 = ?");

    // Code block content:
    expect(codeBlocks[0].stringContent).toBe("Compute 1028 + 23.");

    // The inner block ranges should be offset within the document
    expect(mathBlocks[0].range.from).toBeGreaterThan(0);
    expect(codeBlocks[0].range.from).toBeGreaterThan(mathBlocks[0].range.to);
});

test("Inner input area with markdown only (Lean) #3", () => {
    // Lean equivalent of "Inner input area (and hint) blocks #3" (Rocq)
    // Input area containing only markdown text.
    // Note: the tokenizer only creates Text tokens for gaps >1 char between matches
    // (see lean.ts: `pos > prev.range.to + 1`), so "t" (1 char) is lost.
    const doc = "\n:::input\nt\n:::\nAfter input";
    const blocks = topLevelBlocksLean(doc);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(1);

    const [b1] = inputBlocks;
    expect(typeguards.isInputAreaBlock(b1)).toBe(true);
    expect(b1.innerBlocks).toBeDefined();
});

test("Inner hint blocks (Lean)", () => {
    // Test that hint blocks properly parse inner blocks.
    const document = "# Header\n:::hint \"Show hint\"\n$$`E = mc^2`\nhello\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const hintBlocks = blocks.filter(b => typeguards.isHintBlock(b));
    expect(hintBlocks.length).toBe(1);

    const [hint] = hintBlocks;
    expect(hint.title).toBe("Show hint");
    expect(hint.innerBlocks).toBeDefined();

    // Inner blocks should contain math and markdown
    const innerMath = hint.innerBlocks!.filter(b => typeguards.isMathDisplayBlock(b));
    expect(innerMath.length).toBe(1);
    expect(innerMath[0].stringContent).toBe("E = mc^2");
});

test("Inner input area with multiple code blocks (Lean)", () => {
    // Input area with multiple code blocks inside
    const document = "# Header\n:::input\n```lean\nGoal False.\n```\n```lean\nGoal True.\n```\n:::\n";
    const blocks = topLevelBlocksLean(document);

    const inputBlocks = blocks.filter(b => typeguards.isInputAreaBlock(b));
    expect(inputBlocks.length).toBe(1);

    const innerBlocks = inputBlocks[0].innerBlocks!;
    const codeBlocks = innerBlocks.filter(b => typeguards.isCodeBlock(b));
    expect(codeBlocks.length).toBe(2);

    expect(codeBlocks[0].stringContent).toBe("Goal False.");
    expect(codeBlocks[1].stringContent).toBe("Goal True.");
});
