import { createHintBlocks, createInputBlocks } from "../../editor/src/kroqed-editor/prosedoc-construction/block-extraction";
import { isHintBlock, isInputAreaBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/typeguards";

test("Identify input blocks", () => {
    const document = "# Example\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = createInputBlocks(document);

    expect(blocks.length).toBe(1);
    expect(isInputAreaBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("# Test input area");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(54);
});

test("Identify hint blocks", () => {
    const document = "# Example\n<hint title=\"hint-title-test\">\n# Test hint\n</hint>\n";
    const blocks = createHintBlocks(document);

    expect(blocks.length).toBe(1);
    expect(isHintBlock(blocks[0])).toBe(true);
    expect(blocks[0].title).toBe("hint-title-test");
    expect(blocks[0].stringContent).toBe("# Test hint");
    expect(blocks[0].range.from).toBe(10);
    expect(blocks[0].range.to).toBe(60);
});