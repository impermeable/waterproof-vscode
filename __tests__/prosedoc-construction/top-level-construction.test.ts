import { topLevelBlocksMV } from "../../editor/src/kroqed-editor/prosedoc-construction";
import { isHintBlock, isInputAreaBlock, isMarkdownBlock, isMathDisplayBlock, isCoqBlock } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/typeguards";

const inputDocument = `# Example document
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
test("Parse top level blocks", () => {
    const blocks = topLevelBlocksMV(inputDocument);
    expect(blocks.length).toBe(7);

    expect(isMarkdownBlock(blocks[0])).toBe(true);
    expect(blocks[0].stringContent).toBe("# Example document\n");
    
    expect(isHintBlock(blocks[1])).toBe(true);
    expect(blocks[1].stringContent).toBe("```coq\nRequire Import ZArith.\n```");
    
    expect(isInputAreaBlock(blocks[2])).toBe(true);
    expect(blocks[2].stringContent).toBe("$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```");
    
    expect(isMarkdownBlock(blocks[3])).toBe(true);
    expect(blocks[3].stringContent).toBe("\n#### Markdown content\n");
    
    expect(isMathDisplayBlock(blocks[4])).toBe(true);
    expect(blocks[4].stringContent).toBe(" \int_0^2 x dx ");
    
    expect(isCoqBlock(blocks[5])).toBe(true);
    expect(blocks[5].stringContent).toBe("Compute 1 + 1.");

    expect(isMarkdownBlock(blocks[6])).toBe(true);
    expect(blocks[6].stringContent).toBe("Random Markdown list:\n    1. Item 3\n    2. Item 0\n    3. $1 + 1$\n");
})