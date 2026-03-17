import { BlockRange, typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksLean } from "../../editor/src/document-construction/construct-document";

/**
 * Lean equivalents of the newline block tests in newlineblock.test.ts.
 * Note: In Lean, code blocks require a preceding newline (the regex uses
 * a lookbehind for \n), so some test structures differ slightly from MV.
 */

test("NewlineBlock (Lean) 1", () => {
    // Lean equivalent of "NewlineBlock 1" (Coq)
    // Starting with a newline before a code block
    const input = "\n```lean\nCompute 1 + 1.\n```";
    const blocks = topLevelBlocksLean(input);

    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isNewlineBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("");
    expect(b1.range).toStrictEqual<BlockRange>({from: 0, to: 1});
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Compute 1 + 1.");
    expect(b2.range).toStrictEqual<BlockRange>({from: 1, to: input.length});
});

test("NewlineBlock (Lean) 2", () => {
    // Lean equivalent of "NewlineBlock 2" (Coq)
    // In Lean, code blocks need a preceding newline, so we use markdown before.
    // Note: the trailing \n after \n``` is a non-significant newline and does not
    // produce a separate block (range.to - range.from is 1, below the >1 threshold).
    const input = "Text\n```lean\nCompute 1 + 1.\n```\n";
    const blocks = topLevelBlocksLean(input);

    // Expect: markdown, newline, code (trailing \n is absorbed, not a separate block)
    expect(blocks.length).toBe(3);
    const [md, nl1, code] = blocks;

    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(md.stringContent).toBe("Text");
    expect(md.range).toStrictEqual<BlockRange>({from: 0, to: 4});

    expect(typeguards.isNewlineBlock(nl1)).toBe(true);
    expect(nl1.range).toStrictEqual<BlockRange>({from: 4, to: 5});

    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(code.stringContent).toBe("Compute 1 + 1.");
    expect(code.range).toStrictEqual<BlockRange>({from: 5, to: 31});
    expect(code.innerRange).toStrictEqual<BlockRange>({from: 13, to: 27});
});

test("NewlineBlock (Lean) 3", () => {
    // Lean equivalent of "NewlineBlock 3" (Coq)
    // Newline before a code block; trailing \n after \n``` does not produce a block.
    const input = "\n```lean\nCompute 1 + 1.\n```\n";
    const blocks = topLevelBlocksLean(input);

    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isNewlineBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("");
    expect(b1.range).toStrictEqual<BlockRange>({from: 0, to: 1});
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Compute 1 + 1.");
    expect(b2.range).toStrictEqual<BlockRange>({from: 1, to: 27});
    expect(b2.innerRange).toStrictEqual<BlockRange>({from: 9, to: 23});
});
