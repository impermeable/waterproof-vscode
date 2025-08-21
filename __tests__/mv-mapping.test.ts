
import { TextDocMappingMV as TextDocMapping } from "../editor/src/mapping";
import { ReplaceStep, WaterproofSchema } from "waterproof-editor";
import { expect } from "@jest/globals";
import { FileTranslator } from "waterproof-editor";

test("Normal coqdown", () => {

    expect(TextDocMapping.getNextHTMLtag("<coqdown>").content).toBe("coqdown");
    expect(TextDocMapping.getNextHTMLtag("<coqdown>").start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag("<coqdown>").end).toBe(9);
    expect(TextDocMapping.getNextHTMLtag("<coqdown>").preNumber).toBe(0)
    expect(TextDocMapping.getNextHTMLtag("<coqdown>").postNumber).toBe(0)
});

test("NormalCoqblock", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine">`).content).toBe("coqblock");
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine">`).end).toBe(102);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine">`).preNumber).toBe(2)
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine">`).postNumber).toBe(2)
});

test("NormalCoqblock 1", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="">`).content).toBe("coqblock");
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="">`).end).toBe(95);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="">`).preNumber).toBe(2)
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="">`).postNumber).toBe(1)
});

test("NormalCoqblock 2", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).content).toBe("coqblock");
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).end).toBe(88);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).preNumber).toBe(1)
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).postNumber).toBe(1)
});

test("NormalCoqblock 3", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).content).toBe("coqblock");
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).end).toBe(81);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).preNumber).toBe(0)
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="newLine" prePostWhite="" postPostWhite="">`).postNumber).toBe(1)
});

test("NormalCoqblock 4", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="" prePostWhite="" postPostWhite="">`).content).toBe("coqblock");
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="" prePostWhite="" postPostWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="" prePostWhite="" postPostWhite="">`).end).toBe(74);
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="" prePostWhite="" postPostWhite="">`).preNumber).toBe(0)
    expect(TextDocMapping.getNextHTMLtag(`<coqblock prePreWhite="" postPreWhite="" prePostWhite="" postPostWhite="">`).postNumber).toBe(0)
});

test("Coqdown", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="">`).content).toBe("coqdoc");
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="">`).end).toBe(33);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="">`).preNumber).toBe(0)
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="">`).postNumber).toBe(0)
});

test("coqdoc 1", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="">`).content).toBe("coqdoc");
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="">`).end).toBe(40);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="">`).preNumber).toBe(1)
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="">`).postNumber).toBe(0)
});

test("coqdoc 2", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="newLine">`).content).toBe("coqdoc");
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="newLine">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="newLine">`).end).toBe(40);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="newLine">`).preNumber).toBe(0)
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="" postWhite="newLine">`).postNumber).toBe(1)
});

test("coqdoc 3", () => {
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="newLine">`).content).toBe("coqdoc");
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="newLine">`).start).toBe(0);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="newLine">`).end).toBe(47);
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="newLine">`).preNumber).toBe(1)
    expect(TextDocMapping.getNextHTMLtag(`<coqdoc preWhite="newLine" postWhite="newLine">`).postNumber).toBe(1)
});

test("testMapping", () => {
    const textDocMapping = new TextDocMapping(`<markdown>Hello</markdown>`, 0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(3-2)) {
        //@ts-ignore
        expect(mapping.get(3-2).startProse).toBe(3-2);expect(mapping.get(3-2).endProse).toBe(8-2);expect(mapping.get(3-2).startText).toBe(0);expect(mapping.get(3-2).endText).toBe(5)
    } else {
        throw new Error("Index does not exist")
    }
})

test("testMapping", () => {
    const textDocMapping = new TextDocMapping(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock>`, 0)
    const mapping = textDocMapping.getMapping()
    if (mapping.has(4-2)) {
        //@ts-ignore
        expect(mapping.get(4-2).startProse).toBe(4-2);expect(mapping.get(4-2).endProse).toBe(16-2);expect(mapping.get(4-2).startText).toBe(8);expect(mapping.get(4-2).endText).toBe(20)
    } else {
        throw new Error("Index does not exist")
    }
})

test("testMapping 2", () => {
    const textDocMapping = new TextDocMapping(`<markdown>Hello</markdown><coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock>`, 0)
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
    const textDocMapping = new TextDocMapping(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown>Hello</markdown>`,0)
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
    const textDocMapping = new TextDocMapping(`<coqblock prePreWhite="newLine" postPreWhite="newLine" prePostWhite="newLine" postPostWhite="newLine"><coqdoc preWhite="newLine" postWhite="newLine"><coqdown>This is code</coqdown></coqdoc></coqcode></coqblock>`,0)
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
    const translated = (new FileTranslator()).toProsemirror(docString);
    const textDocMapping = new TextDocMapping(translated,0)
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
    const textDocMapping = new TextDocMapping(`<markdown>Hello</markdown>`,0)
    textDocMapping.getMapping()
    const text = WaterproofSchema.text("Text");
    const coqCode = WaterproofSchema.nodes['coqcode'].create({}, text);
    const moreIntNode = WaterproofSchema.nodes['coqblock'].create({}, coqCode);
    // const slice = node.slice(0);
    const slice = moreIntNode.slice(0)
    new ReplaceStep(1, 1, slice)

})
