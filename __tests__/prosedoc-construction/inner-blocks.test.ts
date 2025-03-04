import { createCoqDocInnerBlocks, createCoqInnerBlocks, createInputAndHintInnerBlocks } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/inner-blocks";
import { isCoqCodeBlock, isCoqDocBlock, isCoqMarkdownBlock, isMathDisplayBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/typeguards";
import { expect } from "@jest/globals";

test("Inner input area (and hint) blocks", () => {
    const inputAreaContent = "$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```";
    
    const blocks = createInputAndHintInnerBlocks(inputAreaContent);

    expect(blocks.length).toBe(2);
    expect(isMathDisplayBlock(blocks[0])).toBe(true);

    // Math display content:
    expect(blocks[0].stringContent).toBe("1028 + 23 = ?");
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(17);

    // CoqBlock content:
    expect(blocks[1].stringContent).toBe("Compute 1028 + 23.");
    expect(blocks[1].range.from).toBe(17);
    expect(blocks[1].range.to).toBe(inputAreaContent.length);
});

test("Inner coq blocks", () => {
    const coqContent = "Compute 1 + 1.\n(** * Header *)";
    const blocks = createCoqInnerBlocks(coqContent);

    // One block for the coq content and one block for the comment.
    expect(blocks.length).toBe(2);
    expect(isCoqCodeBlock(blocks[0])).toBe(true);
    
    expect(blocks[0].stringContent).toBe("Compute 1 + 1.");
    expect(blocks[0].range.from).toBe(0);
    expect(blocks[0].range.to).toBe(14);

    expect(isCoqDocBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("* Header ");
    expect(blocks[1].range.from).toBe(14);
    expect(blocks[1].range.to).toBe(coqContent.length);
    
    expect(blocks[1].innerBlocks?.length).toBe(1);
    expect(isCoqMarkdownBlock(blocks[1].innerBlocks![0])).toBe(true);
});

test("Inner Coqdoc blocks", () => {
    const coqdocContent = "* Header\n$\\text{math display}$";
    const blocks = createCoqDocInnerBlocks(coqdocContent);
    expect(blocks.length).toBe(2);
    expect(isCoqMarkdownBlock(blocks[0])).toBe(true);
    // FIXME: Again the trailing newline.
    expect(blocks[0].stringContent).toBe("* Header\n");
    expect(blocks[0].range).toStrictEqual({ from: 0, to: 9 });

    expect(isMathDisplayBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("\\text{math display}");
    expect(blocks[1].range).toStrictEqual({ from: 9, to: coqdocContent.length });
});