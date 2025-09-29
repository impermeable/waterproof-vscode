
import { BlockRange, DocumentSerializer, typeguards } from "@impermeable/waterproof-editor";
import { vFileParser } from "../../editor/src/document-construction/vFile";
import { TextDocMappingNew } from "../../editor/src/mapping";
import { tagConfigurationV } from "../../editor/src/vFileConfiguration";


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

    // doc = " * Test \nCompute 3 + 3.\n This is some input. \n Another ";


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

    const mapping = new TextDocMappingNew(blocks, 1, tagConfigurationV, new DocumentSerializer(tagConfigurationV)).getMapping();

    expect(mapping.root.range).toStrictEqual<BlockRange>({ from: 0, to: doc.length });
    expect(mapping.root.innerRange).toStrictEqual<BlockRange>({ from: 0, to: doc.length });
    expect(mapping.root.children.length).toBe(7);

    expect(mapping.root.children[0].type).toBe("markdown");
    expect(mapping.root.children[0].range).toStrictEqual<BlockRange>({ from: 0, to: 13 });
    expect(mapping.root.children[0].innerRange).toStrictEqual<BlockRange>({ from: 4, to: 10 });
    expect(mapping.root.children[0].prosemirrorStart).toBe(1);
    expect(mapping.root.children[0].prosemirrorEnd).toBe(7);

    expect(mapping.root.children[1].type).toBe("newline");
    expect(mapping.root.children[1].range).toStrictEqual<BlockRange>({ from: 13, to: 14 });
    expect(mapping.root.children[1].innerRange).toStrictEqual<BlockRange>({ from: 13, to: 14 });
    expect(mapping.root.children[1].prosemirrorStart).toBe(8);
    expect(mapping.root.children[1].prosemirrorEnd).toBe(9);
    
    expect(mapping.root.children[2].type).toBe("code");
    expect(mapping.root.children[2].range).toStrictEqual<BlockRange>({ from: 14, to: 28 });
    expect(mapping.root.children[2].innerRange).toStrictEqual<BlockRange>({ from: 14, to: 28 });
    expect(mapping.root.children[2].prosemirrorStart).toBe(10);
    expect(mapping.root.children[2].prosemirrorEnd).toBe(24);

    expect(mapping.root.children[3].type).toBe("newline");
    expect(mapping.root.children[3].range).toStrictEqual<BlockRange>({ from: 28, to: 29 });
    expect(mapping.root.children[3].innerRange).toStrictEqual<BlockRange>({ from: 28, to: 29 });
    expect(mapping.root.children[3].prosemirrorStart).toBe(25);
    expect(mapping.root.children[3].prosemirrorEnd).toBe(26);

    expect(mapping.root.children[4].type).toBe("input");
    expect(mapping.root.children[4].range).toStrictEqual<BlockRange>({ from: 29, to: 82 });
    expect(mapping.root.children[4].innerRange).toStrictEqual<BlockRange>({ from: 47, to: 66 });
    expect(mapping.root.children[4].children.length).toBe(1);
    expect(mapping.root.children[4].children[0].type).toBe("code");
    expect(mapping.root.children[4].children[0].range).toStrictEqual<BlockRange>({ from: 47, to: 66 });
    expect(mapping.root.children[4].children[0].innerRange).toStrictEqual<BlockRange>({ from: 47, to: 66 });
    expect(mapping.root.children[4].prosemirrorStart).toBe(27);
    expect(mapping.root.children[4].prosemirrorEnd).toBe(46);

    expect(mapping.root.children[5].type).toBe("newline");
    expect(mapping.root.children[5].range).toStrictEqual<BlockRange>({ from: 82, to: 83 });
    expect(mapping.root.children[5].innerRange).toStrictEqual<BlockRange>({ from: 82, to: 83 });
    expect(mapping.root.children[5].prosemirrorStart).toBe(47);
    expect(mapping.root.children[5].prosemirrorEnd).toBe(48);
    
    expect(mapping.root.children[6].type).toBe("markdown");
    expect(mapping.root.children[6].range).toStrictEqual<BlockRange>({ from: 83, to: doc.length });
    expect(mapping.root.children[6].innerRange).toStrictEqual<BlockRange>({ from: 87, to: 94 });
    expect(mapping.root.children[6].prosemirrorStart).toBe(49);
    expect(mapping.root.children[6].prosemirrorEnd).toBe(56);
});