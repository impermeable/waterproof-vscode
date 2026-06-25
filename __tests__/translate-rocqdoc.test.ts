import { rocqdocToMarkdown, translateRocqDoc } from "../editor/src/rocqdoc";

/*
    This test file aims at testing the translate rocqdoc functionality as defined in:
    editor/src/rocqdoc
*/

test("Expect empty input to return empty output", () => {
  expect(translateRocqDoc("")).toBe("");
});

test("Expect comment to be pretty-printed", () => {
  expect(translateRocqDoc("This is just a pretty-printed comment.")).toBe(
    `This is just a pretty-printed comment.`,
  );
});

test("Expect whitespace to still work", () => {
  expect(translateRocqDoc("        This is just a comment.     ")).toBe(
    `        This is just a comment.     `,
  );
});

test("Expect H1 to be replaced", () => {
  expect(translateRocqDoc("* This is a header")).toBe(`# This is a header`);
});

test("Header with paragraph content", () => {
  expect(translateRocqDoc("* Header\nParagraph")).toBe(`# Header\nParagraph`);
});

test("Expect H1 to be able to include asterisks", () => {
  expect(translateRocqDoc("* *This* is a header")).toBe(`# *This* is a header`);
});

test("Expect H2 to be replaced", () => {
  expect(translateRocqDoc("** This is a header")).toBe(`## This is a header`);
});

test("Expect H3 to be replaced", () => {
  expect(translateRocqDoc("*** This is a header")).toBe(`### This is a header`);
});

test("Expect H4 to be replaced", () => {
  expect(translateRocqDoc("**** This is a header")).toBe(
    `#### This is a header`,
  );
});

test("Expect mixed H1 and H2 to be replaced", () => {
  expect(translateRocqDoc("* This is an H1. \n** Here is an H2")).toBe(
    `# This is an H1. \n## Here is an H2`,
  );
});

test("Expect mixed H1 and H3 to be replaced", () => {
  expect(translateRocqDoc("* This is an H1. \n*** Here is an H3")).toBe(
    `# This is an H1. \n### Here is an H3`,
  );
});

test("Expect verbatim to be replaced", () => {
  // Verbatim tags need to be on their own line!
  expect(translateRocqDoc("<<\nThis is verbatim\n>>")).toBe(
    "```\nThis is verbatim\n```",
  );
});

test("Expect default pretty printing character to be replaced", () => {
  expect(translateRocqDoc("Here follows a pretty-printing character: ->")).toBe(
    `Here follows a pretty-printing character: →`,
  );
});

test("Expect default pretty printing characters to be replaced", () => {
  expect(translateRocqDoc("-> <- <= >=")).toBe(`→ ← ≤ ≥`);
});

test("Expect default pretty-printing to be ordered correctly", () => {
  expect(translateRocqDoc("<-> ->")).toBe("↔ →");
});

test("Expect quoted rocq to be replaced", () => {
  expect(translateRocqDoc("[let id := 3] and [3 : nat]")).toBe(
    "`let id := 3` and `3 : nat`",
  );
});

test("Expect quoted rocq to be replaced and behave nicely with nested square brackets", () => {
  expect(
    translateRocqDoc("[let id := fun [T : Type] (x : t) => x in id 0]"),
  ).toBe("`let id := fun [T : Type] (x : t) ⇒ x in id 0`");
});

test("Expect quoted rocq to be replaced and behave nicely with nested square brackets 2", () => {
  expect(
    translateRocqDoc(
      "[let id := fun [T : Type] (x : t) => x in id 0] and [bool]",
    ),
  ).toBe("`let id := fun [T : Type] (x : t) ⇒ x in id 0` and `bool`");
});

test("Expect preformatted vernacular to be replaced", () => {
  expect(translateRocqDoc("[[\nDefinition test := 1.\n]]")).toBe(
    "```\nDefinition test := 1.\n```",
  );
});

test("Preserves whitespace inside rocqdoc comment.", () => {
  expect(translateRocqDoc("Hello whitespace\n   \n")).toBe(
    `Hello whitespace\n   \n`,
  );
});

test("Preserves whitespace inside rocq code cell.", () => {
  expect(
    translateRocqDoc(
      "This is a rocq code cell\n\nHello whitespace.   \n\n   \n",
    ),
  ).toBe(`This is a rocq code cell\n\nHello whitespace.   \n\n   \n`);
});

test("From indented list in Rocqdoc comments, make markdown list", () => {
  expect(
    translateRocqDoc(
      "- First item\n- Second item\n  - Indented item\n  - Second indented item\n- Third item",
    ),
  ).toBe(
    `- First item\n- Second item\n    - Indented item\n    - Second indented item\n- Third item`,
  );
});

test("Replace % inside of rocqdoc", () => {
  expect(rocqdocToMarkdown("%\\text{coqdoc in mathinline?!}%")).toBe(
    "<math-inline>\\text{coqdoc in mathinline?!}</math-inline>",
  );
});
