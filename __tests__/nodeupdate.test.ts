/* eslint-disable @typescript-eslint/ban-ts-comment */
// Disable because the @ts-expect-error clashes with the tests
import { TextDocMappingNew, TreeNode, NodeUpdate } from "../editor/src/kroqed-editor/mappingModel/treestructure";
import { ReplaceStep, ReplaceAroundStep, Step } from "prosemirror-transform";
import { createProseMirrorDocument } from "../editor/src/kroqed-editor/prosedoc-construction/construct-document";
import { WaterproofSchema } from "../editor/src/kroqed-editor/schema";
import { FileFormat, DocChange, WrappingDocChange } from "../shared";
import { expect } from "@jest/globals";
import { EditorState, Transaction, TextSelection } from "prosemirror-state";
import { ParsedPath } from "node:path/win32";
import { ParsedStep } from "../editor/src/kroqed-editor/mappingModel/treestructure/types";
import { lift, wrapIn } from "prosemirror-commands";

function createTestMapping(content: string, build: (s: EditorState) => Transaction): ParsedStep {
    const proseDocandBlocks = createProseMirrorDocument(content, FileFormat.MarkdownV);
    const proseDoc = proseDocandBlocks[0];
    const blocks = proseDocandBlocks[1];
    const mapping = new TextDocMappingNew(blocks, 1)
    let tree = mapping.getMapping();
    const schema = WaterproofSchema;
    const state = EditorState.create({
        schema,
        doc: proseDoc
    });
    const tr = build(state);
    const step = tr.steps.find(
        (s: Step) => s instanceof ReplaceStep || s instanceof ReplaceAroundStep
    );
    if (!step) throw new Error("No Replace step produced by transaction");

    const parsed = NodeUpdate.nodeUpdate(step, tree);
    
    return parsed;
}

test("ReplaceStep delete — removes lone markdown block", () => {
  const content = `Hello`;
  const parsed = createTestMapping(content, (s) => {
    const first = s.doc.child(0);
    const from = 0;
    const to = first.nodeSize;
    return s.tr.delete(from, to);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("");
  expect(parsed.newTree.root!.children.length).toBe(0);
});

test("ReplaceStep delete — removes middle code block, preserves neighbors", () => {
  const content = `before
    \`\`\`coq
    Lemma test
    \`\`\`
    after
    `;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const idx = 1; 
    let pos = 1;
    for (let k = 0; k < idx; k++) pos += s.doc.child(k).nodeSize; 
    const from = pos;
    const to = from + s.doc.child(idx).nodeSize;
    return s.tr.delete(from, to);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("");
  expect(dc.endInFile).toBeGreaterThan(dc.startInFile);

  const children = parsed.newTree.root!.children;
  expect(children.length).toBe(2);
  expect(children[0].type).toBe("markdown");
  expect(children[1].type).toBe("markdown");
  expect(children[0].stringContent).toBe("before\n");
  expect(children[1].stringContent).toBe("after\n");
});

test("ReplaceStep delete — removes nested code inside input wrapper", () => {
  const content = `<input-area>
    \`\`\`coq
    Test
    \`\`\`
    </input-area>`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const wrapper = s.doc.child(0);
    const child = wrapper.child(0);
    const wrapperFrom = 1;
    const from = wrapperFrom + 1;
    const to = from + child.nodeSize;
    return s.tr.delete(from, to);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("");
  expect(dc.endInFile).toBeGreaterThan(dc.startInFile);

  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  const wrapperNode = top[0];
  expect(wrapperNode.children.length).toBe(0);
  expect(wrapperNode.children.some(c => c.type === "code" || c.type === "coqblock")).toBe(false);
});

test("ReplaceStep insert — inserts math_display between blocks", () => {
  const content = `before
\`\`\`coq
Lemma test
\`\`\`
after
`;
  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const math = s.schema.node("math_display", null, s.schema.text("a+b=c\n"));
    const pos =
      1 + s.doc.child(0).nodeSize + s.doc.child(1).nodeSize;
    return s.tr.replaceWith(pos, pos, math);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText.length).toBeGreaterThan(0);
  expect(dc.finalText).toContain("a+b=c");
  expect(parsed.newTree.root!.children.length).toBe(4);
  expect(parsed.newTree.root!.children.some(n => n.stringContent === "a+b=c\n")).toBe(true);
});

test("ReplaceStep insert — inserts code at document start", () => {
  const content = `after
`;
  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const code = s.schema.node("code", null, s.schema.text("X\n"));
    const pos = 1;
    return s.tr.replaceWith(pos, pos, code);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText.length).toBeGreaterThan(0);
  expect(dc.finalText).toContain("X");
  expect(parsed.newTree.root!.children.length).toBe(2);
  const first = parsed.newTree.root!.children[0];
  expect(first.stringContent).toBe("X\n");
});

test("ReplaceStep insert — inserts code inside input wrapper", () => {
  const content = `<input-area>
</input-area>`;
  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const wrapper = s.doc.child(0);
    const pos = 1 + 1;
    const code = s.schema.node("code", null, s.schema.text("Inner\n"));
    return s.tr.replaceWith(pos, pos, code);
  });

  const dc = parsed.result as DocChange;
  expect(dc.finalText.length).toBeGreaterThan(0);
  expect(dc.finalText).toContain("Inner");
  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  const inputNode = top[0];
  expect(inputNode.children.length).toBe(1);
  expect(inputNode.children[0].stringContent).toBe("Inner\n");
});

test("ReplaceAroundStep delete — unwraps single child inside input", () => {
  const content = `<input-area>
\`\`\`coq
A
\`\`\`
</input-area>`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const wrapper = s.doc.child(0);
    const firstChild = wrapper.child(0);
    const from = 1 + 1;
    const to = from + firstChild.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    lift(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText).toBe("");
  expect(wr.secondEdit.finalText).toBe("");
  const children = parsed.newTree.root!.children;
  expect(children.length).toBe(1);
  expect(children[0].type === "code" || children[0].type === "coqblock").toBe(true);
});

test("ReplaceAroundStep delete — unwraps multiple children inside input", () => {
  const content = `<input-area>
Hello
\`\`\`coq
A
\`\`\`
</input-area>`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const wrapper = s.doc.child(0);
    const first = wrapper.child(0);
    const second = wrapper.child(1);
    const from = 1 + 1;
    const to = from + first.nodeSize + second.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    lift(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText).toBe("");
  expect(wr.secondEdit.finalText).toBe("");
  const children = parsed.newTree.root!.children;
  expect(children.length).toBe(2);
  expect(children[0].type).toBe("markdown");
  expect(children[1].type === "code" || children[1].type === "coqblock").toBe(true);
});

test("ReplaceAroundStep delete — unwraps math_display inside input", () => {
  const content = `<input-area>
$
x+y
$
</input-area>`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const wrapper = s.doc.child(0);
    const math = wrapper.child(0);
    const from = 1 + 1;
    const to = from + math.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    lift(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText).toBe("");
  expect(wr.secondEdit.finalText).toBe("");
  const children = parsed.newTree.root!.children;
  expect(children.length).toBe(1);
  expect(children[0].type === "math_display").toBe(true);
});

test("ReplaceAroundStep insert — wraps single markdown in hint", () => {
  const content = `Hello`;
  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const first = s.doc.child(0);
    const from = 1;
    const to = from + first.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    wrapIn(s.schema.nodes.hint)(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText.length).toBeGreaterThan(0);
  expect(wr.secondEdit.finalText.length).toBeGreaterThan(0);
  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  expect(top[0].type).toBe("hint");
  expect(top[0].children.length).toBe(1);
  expect(top[0].children[0].type).toBe("markdown");
  expect(top[0].children[0].stringContent).toBe("Hello");
});

test("ReplaceAroundStep insert — wraps code block in input", () => {
  const content = `\`\`\`coq
X
\`\`\``;

    const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const first = s.doc.child(0);
    const from = 1;
    const to = from + first.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    wrapIn(s.schema.nodes.input)(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText.length).toBeGreaterThan(0);
  expect(wr.secondEdit.finalText.length).toBeGreaterThan(0);
  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  expect(top[0].type).toBe("input");
  expect(top[0].children.length).toBe(1);
  expect(top[0].children[0].type === "code" || top[0].children[0].type === "coqblock").toBe(true);
  expect(top[0].children[0].stringContent).toBe("X\n");
});

test("ReplaceAroundStep insert — wraps math_display in hint", () => {
  const content = `$
a+b
$`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const first = s.doc.child(0);
    const from = 1;
    const to = from + first.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    wrapIn(s.schema.nodes.hint)(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText.length).toBeGreaterThan(0);
  expect(wr.secondEdit.finalText.length).toBeGreaterThan(0);
  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  expect(top[0].type).toBe("hint");
  expect(top[0].children.length).toBe(1);
  expect(top[0].children[0].type).toBe("math_display");
  expect(top[0].children[0].stringContent).toContain("a+b");
});

test("ReplaceAroundStep insert — wraps mixed consecutive blocks in hint", () => {
  const content = `before
\`\`\`coq
Y
\`\`\`
after
`;

  const parsed: ParsedStep = createTestMapping(content, (s: EditorState) => {
    const a = s.doc.child(0);
    const b = s.doc.child(1);
    const c = s.doc.child(2);
    const from = 1;
    const to = from + a.nodeSize + b.nodeSize + c.nodeSize;
    const s2 = s.apply(s.tr.setSelection(TextSelection.create(s.doc, from, to)));
    let out = s2.tr;
    wrapIn(s.schema.nodes.hint)(s2, tr => { out = tr; });
    return out;
  });

  const wr = parsed.result as WrappingDocChange;
  expect(wr.firstEdit.finalText.length).toBeGreaterThan(0);
  expect(wr.secondEdit.finalText.length).toBeGreaterThan(0);
  const top = parsed.newTree.root!.children;
  expect(top.length).toBe(1);
  expect(top[0].type).toBe("hint");
  expect(top[0].children.length).toBe(3);
  expect(top[0].children[0].type).toBe("markdown");
  expect(top[0].children[1].type === "code" || top[0].children[1].type === "coqblock").toBe(true);
  expect(top[0].children[2].type).toBe("markdown");
});

