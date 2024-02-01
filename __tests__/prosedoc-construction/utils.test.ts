import { iteratePairs, sortBlocks } from "../../editor/src/kroqed-editor/prosedoc-construction/utils";

test("Sort blocks #1", () => {
    const stringContent = "";
    const toProseMirror = () => null;
    const testBlocks = [
        {type: "second", range: {from: 1, to: 2}, stringContent, toProseMirror}, 
        {type: "first", range: {from: 0, to: 1}, stringContent, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].type).toBe("first");
    expect(sorted[1].type).toBe("second");
});

test("Sort blocks #2", () => {
    const stringContent = "";
    const toProseMirror = () => null;
    const testBlocks = [
        {type: "second", range: {from: 1, to: 2}, stringContent, toProseMirror}, 
        {type: "first", range: {from: 0, to: 1}, stringContent, toProseMirror},
        {type: "third", range: {from: 2, to: 3}, stringContent, toProseMirror}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(3);
    expect(sorted[0].type).toBe("first");
    expect(sorted[1].type).toBe("second");
    expect(sorted[2].type).toBe("third");
});

// TODO: What is the expected behaviour in this case?
// test("Sort blocks with same range", () => {
//     const stringContent = "";
//     const toProseMirror = () => null;
//     const testBlocks = [
//         {type: "second", range: {from: 0, to: 1}, stringContent, toProseMirror}, 
//         {type: "first", range: {from: 0, to: 1}, stringContent, toProseMirror}
//     ];

//     const sorted = sortBlocks(testBlocks);
//     expect(sorted.length).toBe(2);
//     expect(sorted[0].type).toBe("second");
//     expect(sorted[1].type).toBe("first");
// });

test("Iterate pairs (normal)", () => {
    const input = [1, 2, 3, 4];
    const expectedResult = [3, 5, 7];
    const result = iteratePairs(input, (a, b) => a + b);
    expect(result).toEqual(expectedResult);
});

test("Iterate pairs (single element array)", () => {
    const input = [];
    const expectedResult = [];
    const result = iteratePairs(input, (a, b) => b);
    expect(result).toEqual(expectedResult);
});

test("Iterate pairs (single element array)", () => {
    const input = ["test"];
    const expectedResult = [];
    const result = iteratePairs(input, (a, b) => b.length);
    expect(result).toEqual(expectedResult);
});