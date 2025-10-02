import { coqdocToMarkdown, translateCoqDoc } from "../editor/src/coqdoc";

/*
    This test file aims at testing the translate coqdoc functionality as defined in:
    editor/src/coqdoc
*/

test("Expect empty input to return empty output", () => {
    expect(translateCoqDoc("")).toBe("");
});

test("Expect comment to be pretty-printed", () => {
    expect(translateCoqDoc("This is just a pretty-printed comment.")).toBe(`This is just a pretty-printed comment.`);
});

test("Expect whitespace to still work", () => {
    expect(translateCoqDoc("        This is just a comment.     ")).toBe(`        This is just a comment.     `);
});

test("Expect H1 to be replaced", () => {
    expect(translateCoqDoc("* This is a header")).toBe(`# This is a header`);
});

test("Header with paragraph content", () => {
    expect(translateCoqDoc("* Header\nParagraph")).toBe(`# Header\nParagraph`);
});

test("Expect H1 to be able to include asterisks", () => {
    expect(translateCoqDoc("* *This* is a header")).toBe(`# *This* is a header`);
});

test("Expect H2 to be replaced", () => {
    expect(translateCoqDoc("** This is a header")).toBe(`## This is a header`);
});

test("Expect H3 to be replaced", () => {
    expect(translateCoqDoc("*** This is a header")).toBe(`### This is a header`);
});

test("Expect H4 to be replaced", () => {
    expect(translateCoqDoc("**** This is a header")).toBe(`#### This is a header`);
});

test("Expect mixed H1 and H2 to be replaced", () => {
    expect(translateCoqDoc("* This is an H1. \n** Here is an H2")).toBe(`# This is an H1. \n## Here is an H2`);
});

test("Expect mixed H1 and H3 to be replaced", () => {
    expect(translateCoqDoc("* This is an H1. \n*** Here is an H3")).toBe(`# This is an H1. \n### Here is an H3`);
});

test("Expect verbatim to be replaced", () => {
    // Verbatim tags need to be on their own line!
    expect(translateCoqDoc("<<\nThis is verbatim\n>>")).toBe("```\nThis is verbatim\n```");
});

test("Expect default pretty printing character to be replaced", () => {
    expect(translateCoqDoc("Here follows a pretty-printing character: ->")).toBe(`Here follows a pretty-printing character: →`);
});

test("Expect default pretty printing characters to be replaced", () => {
    expect(translateCoqDoc("-> <- <= >=")).toBe(`→ ← ≤ ≥`);
});

test("Expect default pretty-printing to be ordered correctly", () => {
    expect(translateCoqDoc("<-> ->")).toBe("↔ →");
});

test("Expect quoted coq to be replaced", () => {
    expect(translateCoqDoc("[let id := fun [T : Type] (x : t) => x in id 0]")).toBe("`let id := fun [T : Type] (x : t) ⇒ x in id 0`");
});

test("Expect preformatted vernacular to be replaced", () => {
    expect(translateCoqDoc("[[\nDefinition test := 1.\n]]")).toBe("```\nDefinition test := 1.\n```");
});

test("Preserves whitespace inside coqdoc comment.", () => {
    expect(translateCoqDoc("Hello whitespace\n   \n")).toBe(`Hello whitespace\n   \n`);
});

test("Preserves whitespace inside coq code cell.", () => {
    expect(translateCoqDoc("This is a coq code cell\n\nHello whitespace.   \n\n   \n")).toBe(`This is a coq code cell\n\nHello whitespace.   \n\n   \n`);
});

test("From indented list in Coqdoc comments, make markdown list", () => {

    expect(translateCoqDoc("- First item\n- Second item\n  - Indented item\n  - Second indented item\n- Third item"))
    .toBe(`- First item\n- Second item\n    - Indented item\n    - Second indented item\n- Third item`);
});

test("Replace % inside of coqdoc", () => {
    expect(coqdocToMarkdown("%\\text{coqdoc in mathinline?!}%")).toBe("<math-inline>\\text{coqdoc in mathinline?!}</math-inline>");
});