/* eslint-disable no-useless-escape */

import { HintBlock, typeguards } from "@impermeable/waterproof-editor";
import { parseDocument } from "../../editor/src/document-construction/statemachine"

const exampleDocument = `# Sample Document

Here is some introductory text.
\`\`\`python
def example_function():
    return "Hello, World!"
\`\`\`
<hint title="Important Hint">
This is a hint block with some **markdown** content.

\`\`\`python
# Nested code block inside hint
print("This is a nested code block")
\`\`\`
More hint text.
</hint><input-area>Some concluding text.
$$
E = mc^2
$$</input-area>`;

test("test", () => {
    const blocks = parseDocument(exampleDocument, "python");
    console.log(blocks);

    expect(blocks.length).toBe(4);
    const [b1, b2, b3, b4] = blocks;
    expect(typeguards.isMarkdownBlock(b1)).toBe(true);
    expect(typeguards.isCodeBlock(b2)).toBe(true);
    expect(typeguards.isHintBlock(b3)).toBe(true);
    expect(typeguards.isInputAreaBlock(b4)).toBe(true);

    expect(b1.range.from).toBe(0);
    expect(b1.range.to).toBe(50);
    expect(b1.innerRange.from).toBe(0);
    expect(b1.innerRange.to).toBe(50);
    expect(b1.stringContent).toBe(`# Sample Document

Here is some introductory text.`);

    expect(b2.range.from).toBe(50);
    expect(b2.range.to).toBe(116);
    expect(b2.innerRange.from).toBe(61);
    expect(b2.innerRange.to).toBe(111);
    expect(b2.stringContent).toBe(`def example_function():
    return "Hello, World!"`);

    expect(b3.range.from).toBe(116);
    expect(b3.range.to).toBe(306);
    expect((b3 as HintBlock).title).toBe("Important Hint");
    expect(b3.innerRange.from).toBe(145);
    expect(b3.innerRange.to).toBe(299);

    expect(b4.range.from).toBe(306);
    expect(b4.range.to).toBe(367);
    expect(b4.innerRange.from).toBe(318);
    expect(b4.innerRange.to).toBe(354);

    const [hIn1, hIn2, hIn3] = b3.innerBlocks!;
    expect(typeguards.isMarkdownBlock(hIn1)).toBe(true);
    expect(typeguards.isCodeBlock(hIn2)).toBe(true);
    expect(typeguards.isMarkdownBlock(hIn3)).toBe(true);
    
    expect(hIn1.stringContent).toBe(`
This is a hint block with some **markdown** content.
`);
    expect(hIn1.range.from).toBe(145);
    expect(hIn1.range.to).toBe(199);
    expect(hIn1.innerRange.from).toBe(145);
    expect(hIn1.innerRange.to).toBe(199);
    
    expect(hIn2.stringContent).toBe('# Nested code block inside hint\nprint("This is a nested code block")');
    expect(hIn2.range.from).toBe(199);
    expect(hIn2.range.to).toBe(283);
    expect(hIn2.innerRange.from).toBe(210);
    expect(hIn2.innerRange.to).toBe(278);

    expect(hIn3.stringContent).toBe('More hint text.\n');
    expect(hIn3.range.from).toBe(283);
    expect(hIn3.range.to).toBe(299);
    expect(hIn3.innerRange.from).toBe(283);
    expect(hIn3.innerRange.to).toBe(299);

    const [iIn1, iIn2] = b4.innerBlocks!;
    expect(typeguards.isMarkdownBlock(iIn1)).toBe(true);
    expect(typeguards.isMathDisplayBlock(iIn2)).toBe(true);
    
    expect(iIn1.stringContent).toBe('Some concluding text.\n');
    expect(iIn1.range.from).toBe(318);
    expect(iIn1.range.to).toBe(340);
    expect(iIn1.innerRange.from).toBe(318);
    expect(iIn1.innerRange.to).toBe(340);

    expect(iIn2.stringContent).toBe("\nE = mc^2\n");
    expect(iIn2.range.from).toBe(340);
    expect(iIn2.range.to).toBe(354);
    expect(iIn2.innerRange.from).toBe(342);
    expect(iIn2.innerRange.to).toBe(352);
});

// const topLevelBlocksMV = parseDocument;

// test("Inner input area (and hint) blocks", () => {
//     const inputAreaContent = "$$1028 + 23 = ?$$\n```python\nCompute 1028 + 23.\n```";
    
//     const blocks = parseDocument(inputAreaContent, "python");
//     console.log(blocks);

//     expect(blocks.length).toBe(2);
//     expect(typeguards.isMathDisplayBlock(blocks[0])).toBe(true);

//     // Math display content:
//     expect(blocks[0].stringContent).toBe("1028 + 23 = ?");
//     expect(blocks[0].range.from).toBe(0);
//     expect(blocks[0].range.to).toBe(17);

//     // CoqBlock content:
//     expect(blocks[1].stringContent).toBe("Compute 1028 + 23.");
//     expect(blocks[1].range.from).toBe(17);
//     expect(blocks[1].range.to).toBe(inputAreaContent.length);
// });

// test("Verify newlines are part of the coq tags", () => {
//     const document = "\n```python\nLemma test\n```\n";
//     const blocks = topLevelBlocksMV(document, "python");

//     expect(blocks.length).toBe(1);
//     const [b] = blocks;
//     expect(typeguards.isCodeBlock(b)).toBe(true);
//     expect(b.stringContent).toBe("Lemma test");
//     expect(b.range.from).toBe(0);
//     expect(b.range.to).toBe(document.length);
// });

// test("Inner input area (and hint) blocks #2", () => {
//     const inputAreaContent = "$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```\n";
    
//     const offset = 0;
//     const blocks = parseDocument(inputAreaContent, "python");
//     expect(blocks.length).toBe(2);
//     const [b1, b2] = blocks;

//     expect(typeguards.isMathDisplayBlock(b1)).toBe(true);
//     expect(b1.stringContent).toBe("1028 + 23 = ?");
//     expect(b1.range.from).toBe(0 + offset);
//     expect(b1.range.to).toBe(17 + offset);
//     expect(b1.innerRange.from).toBe(2 + offset);
//     expect(b1.innerRange.to).toBe(15 + offset);

//     expect(typeguards.isCodeBlock(b2)).toBe(true);
//     expect(b2.stringContent).toBe("Compute 1028 + 23.");
//     expect(b2.range.from).toBe(17 + offset);
//     expect(b2.range.to).toBe(48 + offset);
//     expect(b2.innerRange.from).toBe(25 + offset);
//     expect(b2.innerRange.to).toBe(43 + offset);
// });


// const inputDocumentMV = `# Example document
// <hint title="example hint (like for imports)">
// \`\`\`coq
// Require Import ZArith.
// \`\`\`
// </hint>
// <input-area>
// $$1028 + 23 = ?$$
// \`\`\`coq
// Compute 1028 + 23.
// \`\`\`
// </input-area>
// #### Markdown content
// $$ \int_0^2 x dx $$
// \`\`\`coq
// Compute 1 + 1.
// \`\`\`
// Random Markdown list:
//     1. Item 3
//     2. Item 0
//     3. $1 + 1$
// `;


// // FIXME: Add checks for prewhite and postwhite here.
// test("Parse top level blocks (MV)", () => {
//     const blocks = parseDocument(inputDocumentMV, "coq");
//     console.log(blocks);
//     expect(blocks.length).toBe(8);

//     expect(typeguards.isMarkdownBlock(blocks[0])).toBe(true);
//     expect(blocks[0].stringContent).toBe("# Example document\n");

//     expect(typeguards.isHintBlock(blocks[1])).toBe(true);
//     expect(blocks[1].stringContent).toBe("\n```coq\nRequire Import ZArith.\n```\n");

//     expect(typeguards.isMarkdownBlock(blocks[2])).toBe(true);
//     expect((blocks[2] as MarkdownBlock).isNewLineOnly).toBe(true);

//     expect(typeguards.isInputAreaBlock(blocks[3])).toBe(true);
//     expect(blocks[3].stringContent).toBe("\n$$1028 + 23 = ?$$\n```coq\nCompute 1028 + 23.\n```\n");

//     expect(typeguards.isMarkdownBlock(blocks[4])).toBe(true);
//     expect(blocks[4].stringContent).toBe("\n#### Markdown content\n");

//     expect(typeguards.isMathDisplayBlock(blocks[5])).toBe(true);
//     expect(blocks[5].stringContent).toBe(" \int_0^2 x dx ");
    
//     expect(typeguards.isCodeBlock(blocks[6])).toBe(true);
//     expect(blocks[6].stringContent).toBe("Compute 1 + 1.");

//     expect(typeguards.isMarkdownBlock(blocks[7])).toBe(true);
//     expect(blocks[7].stringContent).toBe("Random Markdown list:\n    1. Item 3\n    2. Item 0\n    3. $1 + 1$\n");
// });
