/* eslint-disable @typescript-eslint/ban-ts-comment */
// Disable because the @ts-expect-error clashes with the tests
import { TextDocMappingNew, TreeNode } from "../editor/src/kroqed-editor/mappingModel/treestructure"; 
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
    expect(nodes.length).toBe(2);
    const markdownNode = nodes[1];
    console.log(markdownNode)
    expect(markdownNode.type).toBe("markdown");
    expect(markdownNode.originalStart).toBe(0);
    expect(markdownNode.originalEnd).toBe(5);
    expect(markdownNode.prosemirrorStart).toBe(1);
    expect(markdownNode.prosemirrorEnd).toBe(6);
    expect(markdownNode.stringContent).toBe("Hello");    
})

test("testMapping coqblock with code", () => {
    const content = "```coq\nLemma test\n```";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(2);
    
    // Parent coqblock
    const coqblockNode = nodes[1];
    expect(coqblockNode.type).toBe("code");
    //expect(coqblockNode.originalStart).toBe(7);
    //expect(coqblockNode.originalEnd).toBe(17); 
    expect(coqblockNode.prosemirrorStart).toBe(1); 
    expect(coqblockNode.prosemirrorEnd).toBe(11); 
    expect(coqblockNode.stringContent).toBe("Lemma test");
});

test("Input-area with nested coqblock", () => {
    const content = "<input-area>\n```coq\nTest\n```\n</input-area>";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(3);
    
    // Input-area node
    const inputAreaNode = nodes[1];
    expect(inputAreaNode.type).toBe("input_area");
    expect(inputAreaNode.originalStart).toBe(13);
    //expect(inputAreaNode.originalEnd).toBe(29);
    expect(inputAreaNode.prosemirrorStart).toBe(1); 
    expect(inputAreaNode.prosemirrorEnd).toBe(7); 
    
    // Nested coqblock
    const coqblockNode = nodes[2];
    //expect(coqblockNode.originalStart).toBe(20); 
    //expect(coqblockNode.originalEnd).toBe(24);
    expect(coqblockNode.prosemirrorStart).toBe(2);
    expect(coqblockNode.prosemirrorEnd).toBe(6);

});

// test("Hint block with coq code", () => {
//     const content = `<hint title="Import libraries">\n\`\`\`coq\nRequire Import Rbase.\n\`\`\`\n</hint>`;
//     const nodes = createTestMapping(content);
    
//     expect(nodes.length).toBe(3);
    
//     // Hint node
//     const hintNode = nodes[1];
//     expect(hintNode.type).toBe("hint");
//     expect(hintNode.originalStart).toBe(0);
//     expect(hintNode.originalEnd).toBe(65);
    
//     // Nested coqblock
//     const coqblockNode = nodes[1];
//     expect(coqblockNode.originalStart).toBe(25); 
//     expect(coqblockNode.originalEnd).toBe(53);
    
//     // Nested coqcode
//     const coqcodeNode = nodes[2];
//     expect(coqcodeNode.stringContent).toBe("Require Import Rbase.");
// });

test("Mixed content section", () => {
    const content = `### Example:
\`\`\`coq
Lemma
Test
\`\`\`
<input-area>
\`\`\`coq
(* Your solution here *)
\`\`\`
</input-area>`;
    const nodes = createTestMapping(content);
    console.log(nodes)
    
    // Expected nodes: markdown (header), coqblock, input-area (with coqblock)
    expect(nodes.length).toBe(5);
    
    // Verify markdown header
    const headerNode = nodes[1];
    expect(headerNode.type).toBe("markdown");
    expect(headerNode.stringContent).toContain("### Example:");
    expect(headerNode.originalStart).toBe(0)
    //expect(headerNode.originalEnd).toBe(12)
    expect(headerNode.prosemirrorStart).toBe(1)
    expect(headerNode.prosemirrorEnd).toBe(13)
    
    // Example coqblock
    const exampleCoqblock = nodes[2];
    expect(exampleCoqblock.type).toBe("code");
    //expect(exampleCoqblock.originalStart).toBe(20)
    //expect(exampleCoqblock.originalEnd).toBe(30)
    expect(exampleCoqblock.prosemirrorStart).toBe(15)
    expect(exampleCoqblock.prosemirrorEnd).toBe(25)
    
    // Input-area
    const inputAreaNode = nodes[3];
    expect(inputAreaNode.type).toBe("input_area");
    
    // Nested coqblock inside input-area
    const nestedCoqblock = nodes[4];
    expect(nestedCoqblock.type).toBe("code");
    //expect(nestedCoqblock.originalStart).toBe(55)
    //expect(nestedCoqblock.originalEnd).toBe(79)
    expect(nestedCoqblock.prosemirrorStart).toBe(28)
    expect(nestedCoqblock.prosemirrorEnd).toBe(52)
});

test("Empty coqblock", () => {
    const content = "```coq\n```";
    const nodes = createTestMapping(content);
    
    expect(nodes.length).toBe(2);
    
    // Child coqcode (empty)
    const coqcodeNode = nodes[1];
    expect(coqcodeNode.stringContent).toBe("");
});