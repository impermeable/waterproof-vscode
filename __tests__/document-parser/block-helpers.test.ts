import { sortBlocks } from "../../editor/src/kroqed-editor/new-translator-parser/block-helpers";
import { text } from "../../editor/src/kroqed-editor/new-translator-parser/pm-node-constructors";

test("Sort blocks #1", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 1, to: 2}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].name).toBe("first");
    expect(sorted[1].name).toBe("second");
});

test("Sort blocks #2", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 1, to: 2}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror},
        {name: "third", range: {from: 2, to: 3}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(3);
    expect(sorted[0].name).toBe("first");
    expect(sorted[1].name).toBe("second");
    expect(sorted[2].name).toBe("third");
});

// TODO: What is the expected behaviour in this case?
test("Sort blocks with same range", () => {
    const content = "";
    const toProseMirror = () => text(content);
    const testBlocks = [
        {name: "second", range: {from: 0, to: 1}, content, toProseMirror}, 
        {name: "first", range: {from: 0, to: 1}, content, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].name).toBe("second");
    expect(sorted[1].name).toBe("first");
});