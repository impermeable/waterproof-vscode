import { topLevelBlocksMV, topLevelBlocksV } from "../../editor/src/kroqed-editor/prosedoc-construction";
import { MarkdownBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/blocktypes";
import { isHintBlock, isInputAreaBlock, isMarkdownBlock, isMathDisplayBlock, isCoqBlock, isCoqDocBlock, isCoqCodeBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/typeguards";

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

    expect(isMarkdownBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("# Example document\n");
    
    expect(isHintBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("```coq\nRequire Import ZArith.\n```");
    
    expect(isMarkdownBlock(blocks[2])).toBe(true);
    expect((blocks[2] as MarkdownBlock).isNewLineOnly).toBe(true);

    expect(isInputAreaBlock(blocks[3])).toBe(true);
    expect(blocks[3].stringContent).toBe("\n$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```\n");
    
    expect(isMarkdownBlock(blocks[4])).toBe(true);
    expect(blocks[4].stringContent).toBe("\n#### Markdown content\n");
    
    expect(isMathDisplayBlock(blocks[5])).toBe(true);
    expect(blocks[5].stringContent).toBe(" \int_0^2 x dx ");
    
    expect(isCoqBlock(blocks[6])).toBe(true);
    expect(blocks[6].stringContent).toBe("Compute 1 + 1.");

    expect(isMarkdownBlock(blocks[7])).toBe(true);
    expect(blocks[7].stringContent).toBe("Random Markdown list:\n    1. Item 3\n    2. Item 0\n    3. $1 + 1$\n");
});

const inputDocumentV = `(** * Example v file *)
(* begin hint : testing *)
Compute 2 + 2.
(* end hint *)
(* begin input *)
Lemma testing : True.
Proof.
exact I.
Qed.
(* Proof should now be finished *)
(* end input *)
(** *** End example v file *)
`;

test("Parse top level blocks (V)", () => {
    const blocks = topLevelBlocksV(inputDocumentV);
    // coqblock, hint, input, coqblock

    expect(blocks.length).toBe(4);
    expect(isCoqBlock(blocks[0])).toBe(true);
    expect(isHintBlock(blocks[1])).toBe(true);
    expect(isInputAreaBlock(blocks[2])).toBe(true);
    expect(isCoqBlock(blocks[3])).toBe(true);

    expect(blocks[0].stringContent).toBe("(** * Example v file *)\n");
    expect(blocks[1].stringContent).toBe("```coq\nCompute 2 + 2.\n```");
    expect(blocks[2].stringContent).toBe("```coq\nLemma testing : True.\nProof.\nexact I.\nQed.\n(* Proof should now be finished *)\n```\n");
    expect(blocks[3].stringContent).toBe("(** *** End example v file *)\n");
});