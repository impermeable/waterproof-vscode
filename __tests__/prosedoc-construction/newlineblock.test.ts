import { BlockRange, typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksMV } from "../../editor/src/document-construction/construct-document";


test("NewlineBlock 1", () => {
    const input = "\n```coq\nCompute 1 + 1.\n```";
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isNewlineBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("");
    expect(b1.range).toStrictEqual<BlockRange>({from: 0, to: 1});
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Compute 1 + 1.");
    expect(b2.range).toStrictEqual<BlockRange>({from: 1, to: input.length});
});

test("NewlineBlock 2", () => {
    const input = "```coq\nCompute 1 + 1.\n```\n";
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isCodeBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("Compute 1 + 1.");
    expect(b1.range).toStrictEqual<BlockRange>({from: 0, to: 25});
    expect(b1.innerRange).toStrictEqual<BlockRange>({from: 7, to: 21});
    expect(typeguards.isNewlineBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("");
    expect(b2.range).toStrictEqual<BlockRange>({from: input.length - 1, to: input.length});
    expect(b2.innerRange).toStrictEqual<BlockRange>({from: input.length - 1, to: input.length});
});

test("NewlineBlock 3", () => {
    const input = "\n```coq\nCompute 1 + 1.\n```\n";
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(3);
    const [b1, b2, b3] = blocks;
    expect(typeguards.isNewlineBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("");
    expect(b1.range).toStrictEqual<BlockRange>({from: 0, to: 1});
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Compute 1 + 1.");
    expect(b2.range).toStrictEqual<BlockRange>({from: 1, to: 26});
    expect(b2.innerRange).toStrictEqual<BlockRange>({from: 8, to: 22});
    expect(typeguards.isNewlineBlock(b3)).toBe(true);
    expect(b3.stringContent).toBe("");
    expect(b3.range).toStrictEqual<BlockRange>({from: input.length - 1, to: input.length});
    expect(b3.innerRange).toStrictEqual<BlockRange>({from: input.length - 1, to: input.length});
});