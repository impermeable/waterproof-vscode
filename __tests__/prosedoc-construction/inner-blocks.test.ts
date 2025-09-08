import { createInputAndHintInnerBlocks } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/inner-blocks";
import { isMathDisplayBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/typeguards";
import { expect } from "@jest/globals";

test("Inner input area (and hint) blocks", () => {
    const inputAreaContent = "$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```";
    
    const blocks = createInputAndHintInnerBlocks(inputAreaContent, {from: 0, to: 0});

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
