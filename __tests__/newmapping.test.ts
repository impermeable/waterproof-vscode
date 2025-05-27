/* eslint-disable @typescript-eslint/ban-ts-comment */
// Disable because the @ts-expect-error clashes with the tests
import { TextDocMappingNew, TreeNode } from "../editor/src/kroqed-editor/mappingModel/treestructure"; 
import { ReplaceStep } from "prosemirror-transform";
import { TheSchema } from "../editor/src/kroqed-editor/kroqed-schema";
import { translateMvToProsemirror } from "../editor/src/kroqed-editor/translation/toProsemirror";
import { createProseMirrorDocument } from "../editor/src/kroqed-editor/prosedoc-construction/construct-document";
import { FileFormat } from "../shared";
import { expect } from "@jest/globals";

function createTestMapping(content: string): TreeNode[] {
    const proseDocandBlocks = createProseMirrorDocument(content, FileFormat.MarkdownV);
    const mapping = new TextDocMappingNew(proseDocandBlocks[1], 1)
    const tree = mapping.getMapping();
    const nodes: TreeNode[] = [];
    tree.traverseDepthFirst((node: TreeNode) => {
        nodes.push(node);
    });
    return nodes;
}

test("testMapping", () => {
    const content = `Hello`;
    const nodes = createTestMapping(content);
    expect(nodes.length).toBe(1);
    const markdownNode = nodes[0];
    
    expect(markdownNode.type).toBe("markdown");
    expect(markdownNode.originalStart).toBe(0);
    expect(markdownNode.originalEnd).toBe(5); // "Hello" (length 5)
    expect(markdownNode.prosemirrorStart).toBe(0);
    expect(markdownNode.prosemirrorEnd).toBe(5);
    expect(markdownNode.stringContent).toBe("Hello");    
})

test("Coqblock with code", () => {
    const content = "```coq\nLemma test\n```";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(2);
    
    // Parent coqblock
    const coqblockNode = nodes[0];
    expect(coqblockNode.type).toBe("coqblock");
    expect(coqblockNode.originalStart).toBe(0);
    expect(coqblockNode.originalEnd).toBe(19); // ```coq\nLemma test\n``` (19 chars)
    expect(coqblockNode.prosemirrorStart).toBe(0 - 6); // Subtract ```coq (6 chars)
    expect(coqblockNode.prosemirrorEnd).toBe(19 - 3); // Subtract ``` (3 chars)
    
    // Child coqcode
    const coqcodeNode = nodes[1];
    expect(coqcodeNode.type).toBe("coqcode");
    expect(coqcodeNode.originalStart).toBe(6); // After ```coq\n
    expect(coqcodeNode.originalEnd).toBe(16); // Before \n```
    expect(coqcodeNode.prosemirrorStart).toBe(0); // Inherits parent's adjusted start
    expect(coqcodeNode.prosemirrorEnd).toBe(10); // "Lemma test" (10 chars)
    expect(coqcodeNode.stringContent).toBe("Lemma test");
});

test("Input-area with nested coqblock", () => {
    const content = "<input-area>\n```coq\nTest\n```\n</input-area>";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Input-area node
    const inputAreaNode = nodes[0];
    expect(inputAreaNode.type).toBe("input-area");
    expect(inputAreaNode.originalStart).toBe(0);
    expect(inputAreaNode.originalEnd).toBe(35); // Full input-area tags + content
    expect(inputAreaNode.prosemirrorStart).toBe(0 - 12); // Subtract <input-area> (12 chars)
    expect(inputAreaNode.prosemirrorEnd).toBe(35 - 13); // Subtract </input-area> (13 chars)
    
    // Nested coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.originalStart).toBe(13); // After <input-area>\n
    expect(coqblockNode.originalEnd).toBe(28); // ```coq\nTest\n```
    
    // Nested coqcode
    const coqcodeNode = nodes[2];
    expect(coqcodeNode.originalStart).toBe(19); // After ```coq\n
    expect(coqcodeNode.originalEnd).toBe(23); // "Test"
});

test("Hint block with coq code", () => {
    const content = `<hint title="Import libraries">\n\`\`\`coq\nRequire Import Rbase.\n\`\`\`\n</hint>`;
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Hint node
    const hintNode = nodes[0];
    expect(hintNode.type).toBe("hint");
    expect(hintNode.originalStart).toBe(0);
    expect(hintNode.originalEnd).toBe(65); // Full hint tags + content
    
    // Nested coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.originalStart).toBe(25); // After <hint> tag
    expect(coqblockNode.originalEnd).toBe(53); // ```coq\nRequire Import Rbase.\n```
    
    // Nested coqcode
    const coqcodeNode = nodes[2];
    expect(coqcodeNode.stringContent).toBe("Require Import Rbase.");
});

test("Mixed content section", () => {
    const content = `
## 1. We conclude that

### Example:
\`\`\`coq
Lemma example_reflexivity : 0 = 0.
Proof.
We conclude that (0 = 0).
Qed.
\`\`\`

<input-area>
\`\`\`coq
(* Your solution here *)
\`\`\`
</input-area>
`;
    const nodes = createTestMapping(content);
    
    // Expected nodes: markdown (header), coqblock, input-area (with coqblock)
    expect(nodes.length).toBe(5);
    
    // Verify markdown header
    const headerNode = nodes[0];
    expect(headerNode.type).toBe("markdown");
    expect(headerNode.stringContent).toContain("We conclude that");
    
    // Example coqblock
    const exampleCoqblock = nodes[1];
    expect(exampleCoqblock.type).toBe("coqblock");
    
    // Input-area
    const inputAreaNode = nodes[2];
    expect(inputAreaNode.type).toBe("input-area");
    
    // Nested coqblock inside input-area
    const nestedCoqblock = nodes[3];
    expect(nestedCoqblock.type).toBe("coqblock");
});

test("Empty coqblock", () => {
    const content = "```coq\n```";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(2);
    
    // Parent coqblock
    const coqblockNode = nodes[0];
    expect(coqblockNode.originalEnd - coqblockNode.originalStart).toBe(6); // ```coq``` (6 chars)
    
    // Child coqcode (empty)
    const coqcodeNode = nodes[1];
    expect(coqcodeNode.stringContent).toBe("");
});