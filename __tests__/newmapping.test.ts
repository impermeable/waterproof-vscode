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

// Not sure about the values for prosemirrorStart and prosemirrorEnd
test("testMapping", () => {
    const content = `Hello`;
    const nodes = createTestMapping(content);
    expect(nodes.length).toBe(1);
    const markdownNode = nodes[1];
    
    expect(markdownNode.type).toBe("markdown");
    expect(markdownNode.originalStart).toBe(0);
    expect(markdownNode.originalEnd).toBe(5);
    expect(markdownNode.prosemirrorStart).toBe(0);
    expect(markdownNode.prosemirrorEnd).toBe(5);
    expect(markdownNode.stringContent).toBe("Hello");    
})

test("testMapping coqblock with code", () => {
    const content = "```coq\nLemma test\n```";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Parent coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.type).toBe("coqblock");
    expect(coqblockNode.originalStart).toBe(0);
    expect(coqblockNode.originalEnd).toBe(19); 
    expect(coqblockNode.prosemirrorStart).toBe(6); 
    expect(coqblockNode.prosemirrorEnd).toBe(16); 

    // Child coqcode
    const coqcodeNode = nodes[2];
    expect(coqcodeNode.type).toBe("coqcode");
    expect(coqcodeNode.originalStart).toBe(6); 
    expect(coqcodeNode.originalEnd).toBe(16);
    expect(coqcodeNode.prosemirrorStart).toBe(0); 
    expect(coqcodeNode.prosemirrorEnd).toBe(10); 
    expect(coqcodeNode.stringContent).toBe("Lemma test");
});

test("Input-area with nested coqblock", () => {
    const content = "<input-area>\n```coq\nTest\n```\n</input-area>";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Input-area node
    const inputAreaNode = nodes[1];
    expect(inputAreaNode.type).toBe("input-area");
    expect(inputAreaNode.originalStart).toBe(0);
    expect(inputAreaNode.originalEnd).toBe(35);
    expect(inputAreaNode.prosemirrorStart).toBe(12); 
    expect(inputAreaNode.prosemirrorEnd).toBe(32); 
    
    // Nested coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.originalStart).toBe(13); 
    expect(coqblockNode.originalEnd).toBe(28);
    
    // Nested coqcode
    const coqcodeNode = nodes[2];
    expect(coqcodeNode.originalStart).toBe(19);
    expect(coqcodeNode.originalEnd).toBe(23);
});

test("Hint block with coq code", () => {
    const content = `<hint title="Import libraries">\n\`\`\`coq\nRequire Import Rbase.\n\`\`\`\n</hint>`;
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Hint node
    const hintNode = nodes[1];
    expect(hintNode.type).toBe("hint");
    expect(hintNode.originalStart).toBe(0);
    expect(hintNode.originalEnd).toBe(65);
    
    // Nested coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.originalStart).toBe(25); 
    expect(coqblockNode.originalEnd).toBe(53);
    
    // Nested coqcode
    const coqcodeNode = nodes[2];
    expect(coqcodeNode.stringContent).toBe("Require Import Rbase.");
});

test("Mixed content section", () => {
    const content = `
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
    const headerNode = nodes[1];
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
    const coqblockNode = nodes[1];
    expect(coqblockNode.originalEnd - coqblockNode.originalStart).toBe(6); 
    
    // Child coqcode (empty)
    const coqcodeNode = nodes[1];
    expect(coqcodeNode.stringContent).toBe("");
});