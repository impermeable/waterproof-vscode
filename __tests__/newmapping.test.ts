/* eslint-disable @typescript-eslint/ban-ts-comment */
// Disable because the @ts-expect-error clashes with the tests
import { TextDocMappingNew } from "../editor/src/kroqed-editor/mappingModel/treestructure"; 
import { ReplaceStep } from "prosemirror-transform";
import { TheSchema } from "../editor/src/kroqed-editor/kroqed-schema";
import { translateMvToProsemirror } from "../editor/src/kroqed-editor/translation/toProsemirror";
import { expect } from "@jest/globals";

test("testMapping", () => {
    const textDocMapping = new TextDocMappingNew(`<markdown>Hello</markdown>`, 0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(3-2)) {
        //@ts-ignore
        expect(mapping.get(3-2).startProse).toBe(3-2);expect(mapping.get(3-2).endProse).toBe(8-2);expect(mapping.get(3-2).startText).toBe(0);expect(mapping.get(3-2).endText).toBe(5)
    } else {
        throw new Error("Index does not exist")
    }
})

test("testMapping", () => {
    const textDocMapping = new TextDocMappingNew(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock>`, 0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(4-2)) {
        //@ts-ignore
        expect(mapping.get(4-2).startProse).toBe(4-2);expect(mapping.get(4-2).endProse).toBe(16-2);expect(mapping.get(4-2).startText).toBe(8);expect(mapping.get(4-2).endText).toBe(20)
    } else {
        throw new Error("Index does not exist")
    }
})

test("testMapping 2", () => {
    const textDocMapping = new TextDocMappingNew(`<markdown>Hello</markdown><coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock>`, 0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(3-2)) {
        //@ts-ignore
        expect(mapping.get(3-2).startProse).toBe(3-2);expect(mapping.get(3-2).endProse).toBe(8-2);expect(mapping.get(3-2).startText).toBe(0);expect(mapping.get(3-2).endText).toBe(5)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(11-2)) {
        //@ts-ignore
        expect(mapping.get(11-2).startProse).toBe(11-2);expect(mapping.get(11-2).endProse).toBe(23-2);expect(mapping.get(11-2).startText).toBe(13);expect(mapping.get(11-2).endText).toBe(25)
    } else {
        throw new Error("Index does not exist")
    }
    
})

test("testMapping 3", () => {
    const textDocMapping = new TextDocMappingNew(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown>Hello</markdown>`,0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(4-2)) {
        //@ts-ignore
        expect(mapping.get(4-2).startProse).toBe(4-2);expect(mapping.get(4-2).endProse).toBe(16-2);expect(mapping.get(4-2).startText).toBe(8);expect(mapping.get(4-2).endText).toBe(20)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(19-2)) {
        //@ts-ignore
        expect(mapping.get(19-2).startProse).toBe(19-2);expect(mapping.get(19-2).endProse).toBe(24-2);expect(mapping.get(19-2).startText).toBe(25);expect(mapping.get(19-2).endText).toBe(30)
    } else {
        throw new Error("Index does not exist")
    }
    
})

test("testMapping 4", () => {
    const textDocMapping = new TextDocMappingNew(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqdoc preWhite="newLine" postWhite="newLine"><coqdown>This is code</coqdown></coqdoc></coqcode></coqblock>`,0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(5-2)) {
        //@ts-ignore
        expect(mapping.get(5-2).startProse).toBe(5-2);expect(mapping.get(5-2).endProse).toBe(17-2);expect(mapping.get(5-2).startText).toBe(13);expect(mapping.get(5-2).endText).toBe(25)
    } else {
        throw new Error("Index does not exist")
    }
    
})

test("docString", () => {
    const docString = `Hello\n\`\`\`coq\nNo edit pls.\n\`\`\`\n<input-area>HELLO</input-area>\n<hint title="optional">## Header</hint>\n\n\`\`\`coq\nNo edit pls.\n\`\`\``
    const translated = translateMvToProsemirror(docString)
    const textDocMapping = new TextDocMappingNew(translated,0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(3-2)) {
        //@ts-ignore
        expect(mapping.get(3-2).startProse).toBe(3-2);expect(mapping.get(3-2).endProse).toBe(8-2);expect(mapping.get(3-2).startText).toBe(0);expect(mapping.get(3-2).endText).toBe(5)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(11-2)) {
        //@ts-ignore
        expect(mapping.get(11-2).startProse).toBe(11-2);expect(mapping.get(11-2).endProse).toBe(23-2);expect(mapping.get(11-2).startText).toBe(13);expect(mapping.get(11-2).endText).toBe(25)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(27-2)) {
        //@ts-ignore
        expect(mapping.get(27-2).startProse).toBe(27-2);expect(mapping.get(27-2).endProse).toBe(32-2);expect(mapping.get(27-2).startText).toBe(42);expect(mapping.get(27-2).endText).toBe(47)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(35-2)) {
        //@ts-ignore
        expect(mapping.get(35-2).startProse).toBe(35-2);expect(mapping.get(35-2).endProse).toBe(36-2);expect(mapping.get(35-2).startText).toBe(60);expect(mapping.get(35-2).endText).toBe(61)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(39-2)) {
        //@ts-ignore
        expect(mapping.get(39-2).startProse).toBe(39-2);expect(mapping.get(39-2).endProse).toBe(48-2);expect(mapping.get(39-2).startText).toBe(84);expect(mapping.get(39-2).endText).toBe(93)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(51-2)) {
        //@ts-ignore
        expect(mapping.get(51-2).startProse).toBe(51-2);expect(mapping.get(51-2).endProse).toBe(52-2);expect(mapping.get(51-2).startText).toBe(100);expect(mapping.get(51-2).endText).toBe(101)
    } else {
        throw new Error("Index does not exist")
    }
    if (mapping.has(55-2)) {
        //@ts-ignore
        expect(mapping.get(55-2).startProse).toBe(55-2);expect(mapping.get(55-2).endProse).toBe(67-2);expect(mapping.get(55-2).startText).toBe(109);expect(mapping.get(55-2).endText).toBe(121)
    } else {
        throw new Error("Index does not exist")
    }
})

test("test", () => {
    // TODO: Check if this test does anything
    const textDocMapping = new TextDocMappingNew(`<markdown>Hello</markdown>`,0)
    textDocMapping.getMapping()
    const text = TheSchema.text("Text");
    const coqCode = TheSchema.nodes['coqcode'].create({}, text);
    const moreIntNode = TheSchema.nodes['coqblock'].create({}, coqCode);
    // const slice = node.slice(0);
    const slice = moreIntNode.slice(0)
    new ReplaceStep(1, 1, slice)

})
