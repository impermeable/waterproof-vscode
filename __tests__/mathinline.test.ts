import { toMathInline } from "../editor/src/kroqed-editor/translation/toProsemirror/parser"


test("Replace $ inside of markdown", () => {
    expect(toMathInline("markdown", "$\\text{math-inline}$")).toBe("<math-inline>\\text{math-inline}</math-inline>");
});

test("Replace $ inside of markdown with content", () => {
    expect(toMathInline("markdown", "Content\n$\\text{math-inline}$ content in the line\nMore content")).toBe("Content\n<math-inline>\\text{math-inline}</math-inline> content in the line\nMore content");
});

test("Replace % inside of coqdoc", () => {
    expect(toMathInline("coqdoc", "%\\text{coqdoc in mathinline?!}%")).toBe("<math-inline>\\text{coqdoc in mathinline?!}</math-inline>");
});