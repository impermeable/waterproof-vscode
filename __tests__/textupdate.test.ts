import { Mapping } from "../editor/src/mapping";
import { topLevelBlocksMV } from "../editor/src/document-construction/construct-document";
import { DocChange, DocumentSerializer, Fragment, markdown, ReplaceStep, Slice, WaterproofSchema } from "@impermeable/waterproof-editor";
import { TextUpdate } from "../editor/src/mapping/textUpdate";


function createDocAndMapping(doc: string) {
  const blocks = topLevelBlocksMV(doc);
  const mapping = new Mapping(blocks, 0, markdown.configuration("coq"), new DocumentSerializer(markdown.configuration("coq")));
  return mapping;
}

test("ReplaceStep insert — inserts text into a block", () => {
  const content = `Hello`;
  const mapping = createDocAndMapping(content);
  const slice: Slice = new Slice(Fragment.from(WaterproofSchema.text(" world")), 0, 0);
  const step: ReplaceStep = new ReplaceStep(6, 6, slice);
  console.log("here is the step", step);
  const textUpdate = new TextUpdate();
  const {newTree, result} = textUpdate.textUpdate(step, mapping);
  
  const md = newTree.root.children[0];
  expect(md.innerRange.from).toBe(0);
  expect(md.innerRange.to).toBe(11);
  expect(md.range.from).toBe(0);
  expect(md.range.to).toBe(11);
  expect(md.prosemirrorStart).toBe(1);
  expect(md.prosemirrorEnd).toBe(12);
  
  expect(result).toStrictEqual<DocChange>({
    finalText: " world",
    startInFile: 5,
    endInFile: 5
  });
});

test("ReplaceStep insert — inserts text in the middle of a block", () => {
  const content = "Hello world";
  const mapping = createDocAndMapping(content);
  const slice: Slice = new Slice(Fragment.from(WaterproofSchema.text("big ")), 0, 0);
  const step: ReplaceStep = new ReplaceStep(7, 7, slice);
  const textUpdate = new TextUpdate();
  const {newTree, result} = textUpdate.textUpdate(step, mapping);

  const md = newTree.root.children[0];
  
  expect(md.innerRange.from).toBe(0);
  expect(md.innerRange.to).toBe(15);
  expect(md.range.from).toBe(0);
  expect(md.range.to).toBe(15);
  expect(md.prosemirrorStart).toBe(1);
  expect(md.prosemirrorEnd).toBe(16);
  
  expect(result).toStrictEqual<DocChange>({
    finalText: "big ",
    startInFile: 6,
    endInFile: 6
  });
});

test("ReplaceStep delete — deletes part of a block", () => {
  const content = `Hello world`;
  const mapping = createDocAndMapping(content);
  const step: ReplaceStep = new ReplaceStep(7, 12, Slice.empty);
  const textUpdate = new TextUpdate();
  const {newTree, result} = textUpdate.textUpdate(step, mapping);

  const md = newTree.root.children[0];
  expect(md.innerRange.from).toBe(0);
  expect(md.innerRange.to).toBe(6);
  expect(md.range.from).toBe(0);
  expect(md.range.to).toBe(6);
  expect(md.prosemirrorStart).toBe(1);
  expect(md.prosemirrorEnd).toBe(7);

  expect(result).toStrictEqual<DocChange>({
    finalText: "",
    startInFile: 6,
    endInFile: 11
  })
});


test("ReplaceStep replace - replaces part of a block", () => {
  const originalContent = "Hello world";
  const mapping = createDocAndMapping(originalContent);
  const slice: Slice = new Slice(Fragment.from(WaterproofSchema.text("there")), 0, 0);
  const step: ReplaceStep = new ReplaceStep(7, 12, slice);
  const textUpdate = new TextUpdate();
  const {newTree, result} = textUpdate.textUpdate(step, mapping);

  const md = newTree.root.children[0];
  expect(md.innerRange.from).toBe(0);
  expect(md.innerRange.to).toBe(11);
  expect(md.range.from).toBe(0);
  expect(md.range.to).toBe(11);
  expect(md.prosemirrorStart).toBe(1);
  expect(md.prosemirrorEnd).toBe(12);

  // Check that the resulting document change has the correct type (is a DocChange) and has the correct properties.
  expect(result).toStrictEqual<DocChange>({
    finalText: "there",
    startInFile: 6,
    endInFile: 11
  });
});