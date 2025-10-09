import { typeguards } from "@impermeable/waterproof-editor";
import { expect } from "@jest/globals";
import { createInputAndHintInnerBlocks } from "../../editor/src/document-construction/inner-blocks";
import { topLevelBlocksMV } from "../../editor/src/document-construction/construct-document";

test("Inner input area (and hint) blocks", () => {
    const inputAreaContent = "$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```";
    
    const blocks = createInputAndHintInnerBlocks(inputAreaContent, {from: 0, to: 0});

    expect(blocks.length).toBe(3);
    const [math, newline, code] = blocks;
    expect(typeguards.isMathDisplayBlock(math)).toBe(true);
    expect(typeguards.isNewlineBlock(newline)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);

    // Math display content:
    expect(math.stringContent).toBe("1028 + 23 = ?");
    expect(math.range.from).toBe(0);
    expect(math.range.to).toBe(17);

    // CoqBlock content:
    expect(code.stringContent).toBe("Compute 1028 + 23.");
    expect(code.range.from).toBe(18);
    expect(code.range.to).toBe(inputAreaContent.length);
});

test("Verify newlines before and after code are translated into newline nodes", () => {
    const document = "\n```coq\nLemma test\n```\n";
    const blocks = topLevelBlocksMV(document);

    expect(blocks.length).toBe(3);
    const [nl, b, nl2] = blocks;
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isCodeBlock(b)).toBe(true);
    expect(typeguards.isNewlineBlock(nl2)).toBe(true);
    expect(b.stringContent).toBe("Lemma test");
    expect(b.range.from).toBe(1);
    expect(b.range.to).toBe(document.length - 1);
});

test("Inner input area (and hint) blocks #2", () => {
    const inputAreaContent = "$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```\n";
    
    const offset = 10;
    const blocks = createInputAndHintInnerBlocks(inputAreaContent, {from: offset, to: 0});
    expect(blocks.length).toBe(4);
    const [b1, _nl, b2, _nl2] = blocks;

    expect(typeguards.isMathDisplayBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("1028 + 23 = ?");
    expect(b1.range.from).toBe(0 + offset);
    expect(b1.range.to).toBe(17 + offset);
    expect(b1.innerRange.from).toBe(2 + offset);
    expect(b1.innerRange.to).toBe(15 + offset);

    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Compute 1028 + 23.");
    expect(b2.range.from).toBe(18 + offset);
    expect(b2.range.to).toBe(47 + offset);
    expect(b2.innerRange.from).toBe(25 + offset);
    expect(b2.innerRange.to).toBe(43 + offset);
});

test("Inner input area (and hint) blocks #3", () => {
    const doc = `<input-area>
t
</input-area>Afteeer hint`;
    const blocks = topLevelBlocksMV(doc);

    expect(blocks.length).toBe(2);
    const [b1, b2] = blocks;
    expect(typeguards.isInputAreaBlock(b1)).toBe(true);
    expect(b1.stringContent).toBe("\nt\n");

    expect(b1.range.from).toBe(0);
    expect(b1.range.to).toBe(28);
    expect(b1.innerRange.from).toBe(12);
    expect(b1.innerRange.to).toBe(15);

    expect(b1.innerBlocks?.length).toBe(1);
    const [inner] = b1.innerBlocks!;
    expect(typeguards.isMarkdownBlock(inner)).toBe(true);
    expect(inner.stringContent).toBe("\nt\n");
    expect(inner.range.from).toBe(12);
    expect(inner.range.to).toBe(15);
    expect(inner.innerRange.from).toBe(12);
    expect(inner.innerRange.to).toBe(15);

    expect(typeguards.isMarkdownBlock(b2)).toBe(true);
    expect(b2.stringContent).toBe("Afteeer hint");
    expect(b2.range.from).toBe(28);
    expect(b2.range.to).toBe(doc.length);
    expect(b2.innerRange.from).toBe(28);
    expect(b2.innerRange.to).toBe(doc.length);
});