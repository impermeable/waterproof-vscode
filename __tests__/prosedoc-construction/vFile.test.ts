
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