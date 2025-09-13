/* eslint-disable no-useless-escape */
// Disable due to latex code in sample data

import { expect } from '@jest/globals';
import { MarkdownBlock, typeguards } from "@impermeable/waterproof-editor";
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
