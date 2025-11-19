/* eslint-disable no-useless-escape */
// Disable due to latex code in sample data

import { BlockRange, MarkdownBlock, typeguards } from "@impermeable/waterproof-editor";
import { topLevelBlocksMV } from "../../editor/src/document-construction/construct-document";
import { topLevelBlocksLean } from "../../editor/src/document-construction/lean";

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

const inputDocumentLean = `# A Header
::::multilean
\`\`\`lean
def fortyTwo :=
  30 +
\`\`\`
:::input
\`\`\`lean
  12
\`\`\`
:::
::::
## Markdown Content
$$\`x^2 + y = z\`
A list:
  1. *Italicized* text
  2. $\`y = z - x^2\`
`;


// FIXME: Add checks for prewhite and postwhite here.
test("Parse top level blocks (MV)", () => {
    const blocks = topLevelBlocksMV(inputDocumentMV);
    expect(blocks.length).toBe(10);

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

    expect(typeguards.isNewlineBlock(blocks[6])).toBe(true);

    expect(typeguards.isCodeBlock(blocks[7])).toBe(true);
    expect(blocks[7].stringContent).toBe("Compute 1 + 1.");

    expect(typeguards.isNewlineBlock(blocks[8])).toBe(true);

    expect(typeguards.isMarkdownBlock(blocks[9])).toBe(true);
    expect(blocks[9].stringContent).toBe("Random Markdown list:\n    1. Item 3\n    2. Item 0\n    3. $1 + 1$\n");
});

test("Markdown and Code", () => {
    const input = `Test
\`\`\`coq
Compute 3 + 3.
\`\`\``;
    const blocks = topLevelBlocksMV(input);
    expect(blocks.length).toBe(3);

    const [md, nl, code] = blocks;

    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(md.stringContent).toBe("Test");
    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 4 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 0, to: 4 });

    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(nl.stringContent).toBe("");
    expect(nl.range).toStrictEqual<BlockRange>({ from: 4, to: 5 });
    expect(nl.innerRange).toStrictEqual<BlockRange>({ from: 4, to: 5 });

    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(code.stringContent).toBe("Compute 3 + 3.");
    expect(code.range).toStrictEqual<BlockRange>({ from: 5, to:  input.length });
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
    expect(ia.innerBlocks).toBeDefined();
    expect(ia.innerBlocks?.length).toBe(4);

    const [math, nl, code, nl2] = ia.innerBlocks!;
    expect(typeguards.isMathDisplayBlock(math)).toBe(true);
    expect(typeguards.isCodeBlock(code)).toBe(true);
    expect(typeguards.isNewlineBlock(nl)).toBe(true);
    expect(typeguards.isNewlineBlock(nl2)).toBe(true);

    expect(math.stringContent).toBe("a^2 + b^2 = c^2");
    expect(math.range).toStrictEqual<BlockRange>({ from: 12, to: 12 + "$$a^2 + b^2 = c^2$$".length });
    expect(math.innerRange).toStrictEqual<BlockRange>({ from: 12 + 2, to: 12 + "$$a^2 + b^2 = c^2$$".length - 2 });

    expect(nl.range).toStrictEqual<BlockRange>({ from: 12 + "$$a^2 + b^2 = c^2$$".length, to: 12 + "$$a^2 + b^2 = c^2$$".length + 1 });
    expect(nl.innerRange).toStrictEqual<BlockRange>({ from: 12 + "$$a^2 + b^2 = c^2$$".length, to: 12 + "$$a^2 + b^2 = c^2$$".length + 1 });

    expect(code.stringContent).toBe("Lemma trivial : True.\nProof. auto. Qed.");
    expect(code.range).toStrictEqual<BlockRange>({ from: 32, to: ia.range.to - "</input-area>".length - 1});
    expect(code.innerRange).toStrictEqual<BlockRange>({ from: 32 + "```coq\n".length, to: ia.range.to - "</input-area>".length - "\n```\n".length });

    expect(nl2.range).toStrictEqual<BlockRange>({ from: ia.range.to - "</input-area>".length - 1, to: ia.range.to - "</input-area>".length });
    expect(nl2.innerRange).toStrictEqual<BlockRange>({ from: ia.range.to - "</input-area>".length - 1, to: ia.range.to - "</input-area>".length });
});

test("Markdown and input", () => {
    const input = `# Header<input-area>
\`\`\`coq
Goal False.
\`\`\`
\`\`\`coq
Goal True.
\`\`\`
</input-area>`;
    const blocks = topLevelBlocksMV(input);

    expect(blocks.length).toBe(2);
    const [md, ia] = blocks;

    expect(typeguards.isMarkdownBlock(md)).toBe(true);
    expect(md.stringContent).toBe("# Header");
    expect(md.range).toStrictEqual<BlockRange>({ from: 0, to: 8 });
    expect(md.innerRange).toStrictEqual<BlockRange>({ from: 0, to: 8 });

    expect(typeguards.isInputAreaBlock(ia)).toBe(true);
    expect(ia.stringContent).toBe("\n```coq\nGoal False.\n```\n```coq\nGoal True.\n```\n");
    expect(ia.range).toStrictEqual<BlockRange>({ from: 8, to: input.length });
    expect(ia.innerRange).toStrictEqual<BlockRange>({ from: 8 + "<input-area>".length, to: input.length - "</input-area>".length });
    expect(ia.innerBlocks).toBeDefined();


    expect(ia.innerBlocks?.length).toBe(5);


});

test("Parse top level blocks (Lean)", () => {
    const blocks = topLevelBlocksLean(inputDocumentLean);
    expect(blocks.length).toBe(6);

    expect(typeguards.isMarkdownBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("# A Header\n")

    expect(typeguards.isCodeBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("def fortyTwo :=\n  30 +")

    expect(typeguards.isInputAreaBlock(blocks[2])).toBe(true);
    expect(blocks[2].stringContent).toBe("```lean\n  12\n```");

    expect(typeguards.isMarkdownBlock(blocks[3])).toBe(true);
    expect(blocks[3].stringContent).toBe("\n## Markdown Content\n");

    expect(typeguards.isMathDisplayBlock(blocks[4])).toBe(true);
    expect(blocks[4].stringContent).toBe("x^2 + y = z");

    expect(typeguards.isMarkdownBlock(blocks[5])).toBe(true);
    expect(blocks[5].stringContent)
        .toBe("\nA list:\n  1. *Italicized* text\n  2. $`y = z - x^2`\n");
})
