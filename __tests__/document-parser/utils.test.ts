import { Block } from "../../editor/src/kroqed-editor/new-translator-parser/blocks";
import { text } from "../../editor/src/kroqed-editor/new-translator-parser/pm-node-constructors";
import { extractInterBlockRanges } from "../../editor/src/kroqed-editor/new-translator-parser/utils";

test("Extract inter-block ranges", () => {
    const toProseMirror = () => text("test");
    const name = "test";
    const content = "test";

    const document = "Hello, this is a test document, I am testing this document. Test test test test."

    const blocks: Block[] = [
        { range: { from: 0, to: 10 }, name, content, toProseMirror },
        { range: { from: 15, to: 20 }, name, content, toProseMirror },
        { range: { from: 25, to: 30 }, name, content, toProseMirror },
    ];

    const interBlockRanges = extractInterBlockRanges(blocks, document);

    expect(interBlockRanges.length).toBe(3);
    expect(interBlockRanges[0]).toEqual({ from: 10, to: 15 });
    expect(interBlockRanges[1]).toEqual({ from: 20, to: 25 });
    expect(interBlockRanges[2]).toEqual({ from: 30, to: document.length })
});

test("Extract inter-block ranges with no blocks", () => {
    const document = "Hello, this is a test document, I am testing this document. Test test test test."

    const blocks: Block[] = [];

    const interBlockRanges = extractInterBlockRanges(blocks, document);

    expect(interBlockRanges.length).toBe(1);
    expect(interBlockRanges[0]).toEqual({ from: 0, to: document.length });
});