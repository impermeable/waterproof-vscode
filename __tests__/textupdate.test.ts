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
  return TextUpdate.textUpdate(step, mapping);
}

test("ReplaceStep insert — inserts text into a block", () => {
  const content = `Hello`;
  const parsed = createTextUpdateMapping(content, (s) => {
    const pos = 6; // after 'Hello'
    return s.tr.insertText(" world", pos);
  });



  const dc = parsed.result as DocChange;
  expect(dc.finalText).toBe(" world");
  expect(dc.startInFile).toBe(6); // insert after "Hello"
  expect(dc.endInFile).toBe(6);
});

