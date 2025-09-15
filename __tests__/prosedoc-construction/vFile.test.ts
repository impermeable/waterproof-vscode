
import { BlockRange, typeguards } from "@impermeable/waterproof-editor";
import { vFileParser } from "../../editor/src/document-construction/vFile";

const doc = `(** * Test *)
Compute 3 + 3.
(* begin details : test *)
(** Here is a hint *)
(* end details *)(* begin input *)
Check 3.
(* end input *)`


test("", () => {
    const blocks = vFileParser(doc);
    console.log(blocks);
    expect(blocks.length).toBe(4);

    const [b1, b2, b3, b4] = blocks;
    expect(typeguards.isMarkdownBlock(b1)).toBe(true);
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(typeguards.isHintBlock(b3)).toBe(true);
    expect(typeguards.isInputAreaBlock(b4)).toBe(true);

    expect(b1.range).toStrictEqual<BlockRange>({ from: 0, to: 13 });
    expect(b1.innerRange).toStrictEqual<BlockRange>({ from: 4, to: 10 });
    expect(b1.stringContent).toBe("* Test");

    expect(b2.range).toStrictEqual<BlockRange>({ from: 13, to: 29 });
    expect(b2.innerRange).toStrictEqual<BlockRange>({ from: 13, to: 29 });
    expect(b2.stringContent).toBe("Compute 3 + 3.");

    expect(b3.range).toStrictEqual<BlockRange>({ from: 29, to:  95});
    expect(b3.innerRange).toStrictEqual<BlockRange>({ from: 56, to:  77});
    expect(b3.stringContent).toBe("(** Here is a hint *)");

    expect(b4.range).toStrictEqual<BlockRange>({ from: 95, to:  137});
    expect(b4.innerRange).toStrictEqual<BlockRange>({ from: 113, to: 121 });
    expect(b4.stringContent).toBe("Check 3.");

    const [hIn] = b3.innerBlocks!;
    expect(typeguards.isMarkdownBlock(hIn)).toBe(true);
    expect(hIn.range).toStrictEqual<BlockRange>({ from: 56, to:  77 });
    expect(hIn.innerRange).toStrictEqual<BlockRange>({ from: 60, to: 74 });
    expect(hIn.stringContent).toBe("Here is a hint");

    const [iIn] = b4.innerBlocks!;
    expect(typeguards.isCodeBlock(iIn)).toBe(true);
    expect(iIn.range).toStrictEqual<BlockRange>({ from: 113, to: 121 });
    expect(iIn.innerRange).toStrictEqual<BlockRange>({ from: 113, to: 121 });
    expect(iIn.stringContent).toBe("Check 3.");
});