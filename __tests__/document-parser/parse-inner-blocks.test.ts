import { createInnerHintBlocks, createInnerInputAreaBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/block-parsing";
import { isCoqBlock, isMarkdownBlock } from "../../editor/src/kroqed-editor/new-translator-parser/blocks";

test("Parse inner input area blocks", () => {
    const document = "```coq\n(* comment *)\n```";
    const blocks = createInnerInputAreaBlocks(document);

    expect(blocks.length).toBe(1);
    expect(isCoqBlock(blocks[0])).toBe(true);

    expect(blocks[0].content).toBe("(* comment *)");
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(24);
});

test("Parse inner hint blocks", () => {
    const document = "# Title\n```coq\nRequire Import Waterproof.Waterproof.\n```";
    const blocks = createInnerHintBlocks(document);

    expect(blocks.length).toBe(2);
    expect(isMarkdownBlock(blocks[0])).toBe(true);
    expect(isCoqBlock(blocks[1])).toBe(true);

    expect(blocks[0].content).toBe("# Title\n");
    expect(blocks[1].content).toBe("Require Import Waterproof.Waterproof.");

    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(8);

    expect(blocks[1].range.from).toBe(8);
    expect(blocks[1].range.to).toBe(56);
});