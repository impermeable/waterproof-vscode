
import { BlockRange, typeguards } from "@impermeable/waterproof-editor";
import { vFileParser } from "../../editor/src/document-construction/vFile";


test("vFile #1", () => {
    const doc = "(** * Test *)\nCompute 3 + 3.";

    const blocks = vFileParser(doc);
    expect(blocks.length).toBe(3);
    const [md, nl, code] = blocks;
    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);

    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 13 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 4, to: 10 });
    expect(md.stringContent).toBe("* Test");


    expect(nl.range).toStrictEqual<BlockRange>({ from: 13, to: 14 });
    expect(nl.innerRange).toStrictEqual<BlockRange>({ from: 13, to: 14 });

    expect(code.range).toStrictEqual<BlockRange>({ from: 14, to: doc.length });
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 14, to: doc.length });
});

test("vFile #2", () => {
    const doc = "(** * Test *)\nCompute 3 + 3.\n(** Another *)";

    const blocks = vFileParser(doc);

    // console.log(blocks);

    expect(blocks.length).toBe(5);
    const [md, nl, code, nl2, md2] = blocks;
    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(typeguards.isNewlineBlock(nl2)).toBe(true);
    expect(typeguards.isMarkdownBlock(md2)).toBe(true);

    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 13 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 4, to: 10 });
    expect(md.stringContent).toBe("* Test");


    expect(nl.range).toStrictEqual<BlockRange>({ from: 13, to: 14 });
    expect(nl.innerRange).toStrictEqual<BlockRange>({ from: 13, to: 14 });

    expect(code.range).toStrictEqual<BlockRange>({ from: 14, to: 28 });
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 14, to: 28 });

    expect(nl2.range).toStrictEqual<BlockRange>({ from: 28, to: 29 });
    expect(nl2.innerRange).toStrictEqual<BlockRange>({ from: 28, to: 29 });

    expect(md2.range).toStrictEqual<BlockRange>({ from: 29, to: doc.length });
    expect(md2.innerRange).toStrictEqual<BlockRange>({ from: 33, to: 40 });
    expect(md2.stringContent).toBe("Another");
});

test("vFile with input area", () => {
    const doc = "(** * Test *)\nCompute 3 + 3.\n(* begin input *)\nThis is some input.\n(* end input *)\n(** Another *)";

    const blocks = vFileParser(doc);

    expect(blocks.length).toBe(7);

    const [md, nl, code, nl2, input, nl3, md2] = blocks;
    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(typeguards.isNewlineBlock(nl2)).toBe(true);
    expect(typeguards.isInputAreaBlock(input)).toBe(true);
    expect(typeguards.isNewlineBlock(nl3)).toBe(true);
    expect(typeguards.isMarkdownBlock(md2)).toBe(true);

    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 13 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 4, to: 10 });
    expect(md.stringContent).toBe("* Test");

    expect(nl.range).toStrictEqual<BlockRange>({ from: 13, to: 14 });
    expect(nl.innerRange).toStrictEqual<BlockRange>({ from: 13, to: 14 });

    expect(code.range).toStrictEqual<BlockRange>({ from: 14, to: 28 });
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 14, to: 28 });
    expect(code.stringContent).toBe("Compute 3 + 3.");

    expect(nl2.range).toStrictEqual<BlockRange>({ from: 28, to: 29 });
    expect(nl2.innerRange).toStrictEqual<BlockRange>({ from: 28, to: 29 });

    expect(input.range).toStrictEqual<BlockRange>({ from: 29, to:  82 });
    expect(input.innerRange).toStrictEqual<BlockRange>({ from:  47, to:  66 });
    expect(input.stringContent).toBe("This is some input.");

    expect(input.innerBlocks).toBeDefined();
    expect(input.innerBlocks?.length).toBe(1);
    const [inputTextBlock] = input.innerBlocks!;
    expect(typeguards.isCodeBlock(inputTextBlock)).toBe(true);
    expect(inputTextBlock.stringContent).toBe("This is some input.");

    expect(nl3.range).toStrictEqual<BlockRange>({ from: 82, to: 83 });
    expect(nl3.innerRange).toStrictEqual<BlockRange>({ from: 82, to: 83 });

    expect(md2.range).toStrictEqual<BlockRange>({ from: 83, to: doc.length });
    expect(md2.innerRange).toStrictEqual<BlockRange>({ from: 87, to: 94 });
    expect(md2.stringContent).toBe("Another");
});