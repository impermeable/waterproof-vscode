import { TextDocMappingNew } from "../editor/src/kroqed-editor/mappingModel/treestructure";
import { ReplaceStep, Step } from "prosemirror-transform";
import { createProseMirrorDocument } from "../editor/src/kroqed-editor/prosedoc-construction/construct-document";
import { WaterproofSchema } from "../editor/src/kroqed-editor/schema";
import { FileFormat, DocChange } from "../shared";
import { expect } from "@jest/globals";
import { EditorState, Transaction } from "prosemirror-state";
import { ParsedStep } from "../editor/src/kroqed-editor/mappingModel/treestructure/types";
import { TextUpdate } from "../editor/src/kroqed-editor/mappingModel/treestructure/textUpdate";

function createTextUpdateMapping(
  content: string,
  build: (s: EditorState) => Transaction
): ParsedStep {
  const [proseDoc, blocks] = createProseMirrorDocument(
    content,
    FileFormat.MarkdownV
  );
  const mapping = new TextDocMappingNew(blocks, 1);
  //console.log(mapping.getMapping().root)
  const schema = WaterproofSchema;
  const state = EditorState.create({
    schema,
    doc: proseDoc,
  });
  const tr = build(state);
  const step = tr.steps.find((s: Step) => s instanceof ReplaceStep);
  if (!(step instanceof ReplaceStep)) {
    throw new Error("Expected ReplaceStep from transaction");
  }
  const update = TextUpdate.textUpdate(step, mapping);


  return update
}

test("ReplaceStep insert — inserts text into a block", () => {
  const content = `Hello`;
  const parsed = createTextUpdateMapping(content, (s) => {
    const pos = 6; // after 'Hello'
    return s.tr.insertText(" world", pos);
  });

  const newTree = parsed.newTree

  expect(newTree.root?.children[0].originalStart).toBe(0)
  expect(newTree.root?.children[0].originalEnd).toBe(11)
  expect(newTree.root?.children[0].prosemirrorStart).toBe(1)
  expect(newTree.root?.children[0].prosemirrorEnd).toBe(12)

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("Hello world");
  expect(dc.startInFile).toBe(6); // insert after "Hello"
  expect(dc.endInFile).toBe(6);


});

test("ReplaceStep insert — inserts text in the middle of a block", () => {
  const content = `Hello world`;
  const parsed = createTextUpdateMapping(content, (s) => {
    const pos = 7; // between 'Hello ' and 'world'
    return s.tr.insertText("big ", pos);
  });

  const newTree = parsed.newTree;

  expect(newTree.root?.children[0].stringContent).toBe("Hello big world");
  expect(newTree.root?.children[0].originalStart).toBe(0)
  expect(newTree.root?.children[0].originalEnd).toBe(15)
  expect(newTree.root?.children[0].prosemirrorStart).toBe(1)
  expect(newTree.root?.children[0].prosemirrorEnd).toBe(16)

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("Hello big world"); // full updated cell
  expect(dc.startInFile).toBe(6); // after 'Hello '
  expect(dc.endInFile).toBe(6);   // same for insert
});


test("ReplaceStep delete — deletes part of a block", () => {
  const content = `Hello world`;
  const parsed = createTextUpdateMapping(content, (s) => {
    const from = 7; // before 'world'
    const to   = 12; // after 'world'
    return s.tr.delete(from, to);
  });

  const newTree = parsed.newTree;

  expect(newTree.root?.children[0].stringContent).toBe("Hello ");
  expect(newTree.root?.children[0].originalStart).toBe(0)
  expect(newTree.root?.children[0].originalEnd).toBe(6)
  expect(newTree.root?.children[0].prosemirrorStart).toBe(1)
  expect(newTree.root?.children[0].prosemirrorEnd).toBe(7)

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("Hello "); // full updated cell
  expect(dc.startInFile).toBe(6);      // delete starts at space
  expect(dc.endInFile).toBe(11);       // deleted "world"
});

test("ReplaceStep replace — replaces part of a block", () => {
  const content = `Hello world`;
  const parsed = createTextUpdateMapping(content, (s) => {
    const from = 7; // start of 'world'
    const to   = 12; // end of 'world'
    return s.tr.insertText("there", from, to);
  });

  const newTree = parsed.newTree;

  expect(newTree.root?.children[0].stringContent).toBe("Hello there");
  expect(newTree.root?.children[0].originalStart).toBe(0)
  expect(newTree.root?.children[0].originalEnd).toBe(11)
  expect(newTree.root?.children[0].prosemirrorStart).toBe(1)
  expect(newTree.root?.children[0].prosemirrorEnd).toBe(12)

  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe("Hello there"); // full updated cell
  expect(dc.startInFile).toBe(6);
  expect(dc.endInFile).toBe(11);
});

