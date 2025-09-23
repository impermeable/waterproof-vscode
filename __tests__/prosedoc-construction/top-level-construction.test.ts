/* eslint-disable no-useless-escape */
// Disable due to latex code in sample data

import { BlockRange, MarkdownBlock, typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksMV } from "../../editor/src/document-construction/construct-document"

const inputDocumentMV = `# Example document
<hint title="example hint (like for imports)">
\`\`\`coq
Require Import ZArith.
\`\`\`
</hint>
<input-area>
$$1028 + 23 = ?$$
\`\`\`coq
Compute 1028 + 23.
\`\`\`
</input-area>
#### Markdown content
$$ \int_0^2 x dx $$
\`\`\`coq
Compute 1 + 1.
\`\`\`
Random Markdown list:
    1. Item 3
    2. Item 0
    3. $1 + 1$
`;


// FIXME: Add checks for prewhite and postwhite here.
test("Parse top level blocks (MV)", () => {
    const blocks = topLevelBlocksMV(inputDocumentMV);
    expect(blocks.length).toBe(8);

    expect(typeguards.isMarkdownBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("# Example document\n");

    expect(typeguards.isHintBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("\n```coq\nRequire Import ZArith.\n```\n");

    expect(typeguards.isMarkdownBlock(blocks[2])).toBe(true);
    expect((blocks[2] as MarkdownBlock).isNewLineOnly).toBe(true);

    expect(typeguards.isInputAreaBlock(blocks[3])).toBe(true);
    expect(blocks[3].stringContent).toBe("\n$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```\n");

    expect(typeguards.isMarkdownBlock(blocks[4])).toBe(true);
    expect(blocks[4].stringContent).toBe("\n#### Markdown content\n");

    expect(typeguards.isMathDisplayBlock(blocks[5])).toBe(true);
    expect(blocks[5].stringContent).toBe(" \int_0^2 x dx ");
    
    expect(typeguards.isCodeBlock(blocks[6])).toBe(true);
    expect(blocks[6].stringContent).toBe("Compute 1 + 1.");

    expect(typeguards.isMarkdownBlock(blocks[7])).toBe(true);
    expect(blocks[7].stringContent).toBe("Random Markdown list:\n    1. Item 3\n    2. Item 0\n    3. $1 + 1$\n");
});

test("Markdown and Code", () => {
    const input = `Test
\`\`\`coq
Compute 3 + 3.
\`\`\``;
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(2);

    const [md, code] = blocks;

    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(md.stringContent).toBe("Test");    
    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 4 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 0, to: 4 });

    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(code.stringContent).toBe("Compute 3 + 3.");
    expect(code.range).toStrictEqual<BlockRange>({ from: 4, to:  input.length });
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 12, to:  input.length - 4 });
});

test("1 input area with math and code", () => {
    const input = `<input-area>$$a^2 + b^2 = c^2$$
\`\`\`coq
Lemma trivial : True.
Proof. auto. Qed.
\`\`\`
</input-area>`;
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(1);
    const [ia] = blocks;
    
    expect(typeguards.isInputAreaBlock(ia)).toBe(true);
    expect(ia.stringContent).toBe("$$a^2 + b^2 = c^2$$\n```coq\nLemma trivial : True.\nProof. auto. Qed.\n```\n");
    expect(ia.range).toStrictEqual<BlockRange>({ from: 0, to: input.length });
    expect(ia.innerRange).toStrictEqual<BlockRange>({ from: 12, to: input.length - "</input-area>".length });
    expect(ia.innerBlocks?.length).toBe(2);

    const [math, code] = ia.innerBlocks!;
    expect(typeguards.isMathDisplayBlock(math)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);

    expect(math.stringContent).toBe("a^2 + b^2 = c^2");
    expect(math.range).toStrictEqual<BlockRange>({ from: 12, to: 12 + "$$a^2 + b^2 = c^2$$".length });
    expect(math.innerRange).toStrictEqual<BlockRange>({ from: 12 + 2, to: 12 + "$$a^2 + b^2 = c^2$$".length - 2 });

    expect(code.stringContent).toBe("Lemma trivial : True.\nProof. auto. Qed.");
    expect(code.range).toStrictEqual<BlockRange>({ from: 31, to: ia.range.to - "</input-area>".length });
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 31 + "\n```coq\n".length, to: ia.range.to - "</input-area>".length - "\n```\n".length });
});