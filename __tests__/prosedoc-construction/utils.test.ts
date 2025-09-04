import { Block } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks";
import { text } from "../../editor/src/kroqed-editor/prosedoc-construction/blocks/schema";
import { extractInterBlockRanges, iteratePairs, maskInputAndHints, sortBlocks } from "../../editor/src/kroqed-editor/prosedoc-construction/utils";

const toProseMirror = () => text("null");
const debugPrint = () => null;
const innerRange = {from: 0, to: 0};

test("Sort blocks #1", () => {
    const stringContent = "";

    const testBlocks = [
        {type: "second", range: {from: 1, to: 2}, innerRange, stringContent, toProseMirror, debugPrint}, 
        {type: "first", range: {from: 0, to: 1}, innerRange, stringContent, toProseMirror, debugPrint}
    ];

    const sorted = sortBlocks(testBlocks);
    expect(sorted.length).toBe(2);
    expect(sorted[0].type).toBe("first");
    expect(sorted[1].type).toBe("second");
});

test("Sort blocks #2", () => {
    const stringContent = "";

    const testBlocks = [
        {type: "second", range: {from: 1, to: 2}, innerRange, stringContent, toProseMirror, debugPrint}, 
        {type: "first", range: {from: 0, to: 1}, innerRange, stringContent, toProseMirror, debugPrint},
        {type: "third", range: {from: 2, to: 3}, innerRange, stringContent, toProseMirror, debugPrint}
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

test("Mask input and hints #1", () => {
    const inputDocument = "# Example\n<input-area>\n# Test input area\n</input-area>\n";
    const blocks = [
        {type: "input_area", range: {from: 10, to: 54}, innerRange, stringContent: "# Test input area", toProseMirror, debugPrint}
    ];

    const maskedString = "# Example\n                                            \n";
    expect(maskInputAndHints(inputDocument, blocks)).toEqual(maskedString);
});

test("Mask input and hints #2", () => {
    const inputDocument = `<hint title="test">\nThis is a test hint\n<\\hint>\n# Example\n<input-area>\n# Test input area\n</input-area>\n`;
    const blocks = [
        {type: "hint", range: {from: 0, to: 47}, innerRange, stringContent: "This is a test hint", toProseMirror, debugPrint},
        {type: "input_area", range: {from: 58, to: 102}, innerRange, stringContent: "# Test input area", toProseMirror, debugPrint}
    ];

    const maskedString = "                                               \n# Example\n                                            \n";
    expect(maskInputAndHints(inputDocument, blocks)).toEqual(maskedString);
});

test("Extract inter-block ranges", () => {
    const type = "test";
    const stringContent = "test";

    const document = "Hello, this is a test document, I am testing this document. Test test test test."

    const blocks: Block[] = [
        { range: { from: 0, to: 10 }, innerRange, type, stringContent, toProseMirror, debugPrint },
        { range: { from: 15, to: 20 }, innerRange, type, stringContent, toProseMirror, debugPrint },
        { range: { from: 25, to: 30 }, innerRange, type, stringContent, toProseMirror, debugPrint },
    ];

    const interBlockRanges = extractInterBlockRanges(blocks, document);

    expect(interBlockRanges.length).toBe(3);
    expect(interBlockRanges[0]).toEqual({ from: 10, to: 15 });
    expect(interBlockRanges[1]).toEqual({ from: 20, to: 25 });
    expect(interBlockRanges[2]).toEqual({ from: 30, to: document.length })
});

test("Extract inter-block ranges with no blocks", () => {
    const document = "Hello, this is a test document, I am testing this document. Test test test test."

    const blocks: Block[] = [];

    const interBlockRanges = extractInterBlockRanges(blocks, document);

    expect(interBlockRanges.length).toBe(1);
    expect(interBlockRanges[0]).toEqual({ from: 0, to: document.length });
});