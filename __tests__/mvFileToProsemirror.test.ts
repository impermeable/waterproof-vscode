/* eslint-disable no-useless-escape */
// Disable due to test data including latex code
import { translateMvToProsemirror } from "../editor/src/waterproof-editor/translation/toProsemirror/mvFileToProsemirror";
import { expect } from "@jest/globals";

test("Expect empty input to return empty output", () => {
    expect(translateMvToProsemirror("")).toBe("");
});

test("Normal code cell", () => {
    expect(translateMvToProsemirror("```coq\nThis is code\n```")).toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqcode>This is code</coqcode></coqblock>`);
});

test("Normal Text", () => {
    expect(translateMvToProsemirror("This is not code")).toBe(`<markdown>This is not code</markdown>`);
});

test("Normal Header", () => {
    expect(translateMvToProsemirror("# This is a 1 header\n")).toBe(`<markdown># This is a 1 header\n</markdown>`);
});

test("Normal 6 Header", () => {
    expect(translateMvToProsemirror("###### This is a 6 header\n")).toBe(`<markdown>###### This is a 6 header\n</markdown>`);
});

test("Text + code 1", () => {
    expect(translateMvToProsemirror("This is text\n```coq\nThis is code\n```")).toBe(`<markdown>This is text</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqcode>This is code</coqcode></coqblock>`);
});

test("Text + code 2", () => {
    expect(translateMvToProsemirror("```coq\nThis is code\n```\nThis is text")).toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown>This is text</markdown>`);
});

test("Header + code 1", () => {
    expect(translateMvToProsemirror("```coq\nThis is code\n```\n# This is a header\n")).toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown># This is a header\n</markdown>`);
});

test("Header + code 2", () => {
    expect(translateMvToProsemirror("# This is a header\n```coq\nThis is code\n```")).toBe(`<markdown># This is a header</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqcode>This is code</coqcode></coqblock>`);
});

test("Header + text + code 1", () => {
    expect(translateMvToProsemirror("# This is a header\nThis is text\n```coq\nThis is code\n```")).toBe(`<markdown># This is a header\nThis is text</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqcode>This is code</coqcode></coqblock>`);
});

test("Header + text + code 2", () => {
    expect(translateMvToProsemirror("# This is a header\n```coq\nThis is code\n```\nThis is text")).toBe(`<markdown># This is a header</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown>This is text</markdown>`);
});

test("Header + text + code 3", () => {
    expect(translateMvToProsemirror("```coq\nThis is code\n```\n# This is a header\nThis is text")).toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>This is code</coqcode></coqblock><markdown># This is a header\nThis is text</markdown>`);
});

// test("CoqDocTest without text", () => {
//     expect(translateMvToProsemirror("```coq\nThis is code (** coqDoc *)\n```")).toBe(`<codeblock from="coqdoc" globalIndex=0 commentIndex=0 preWhite="" postWhite="">This is code </codeblock><p from="coqdoc" globalIndex=0 commentIndex=0 preCoqBlock=\"\" postCoqBlock=\"\" preCommentWhite=\"\" postCommentWhite=\"\">coqDoc </p>`);
// });

test("Header coqdoc", () => {
    expect(translateMvToProsemirror("```coq\n(** * This is a header*)\n```\n# This is also a header"))
        .toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqdoc preWhite="" postWhite=""><coqdown>* This is a header</coqdown></coqdoc></coqblock><markdown># This is also a header</markdown>`)
})

test("Double coqdoc", () => {
    expect(translateMvToProsemirror("```coq\n(** * This is head*)\n(** This is not head*)\n```"))
    .toBe(`<coqblock prePreWhite="" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqdoc preWhite="" postWhite="newLine"><coqdown>* This is head</coqdown></coqdoc><coqdoc preWhite="" postWhite=""><coqdown>This is not head</coqdown></coqdoc></coqblock>`)
})

test("entire document", () => {
    const docString = `Hello\n\`\`\`coq\nNo edit pls.\n\`\`\`\n<input-area>HELLO</input-area>\n<hint title="optional">## Header</hint>\n\n\`\`\`coq\nNo edit pls.\n\`\`\``
    const predict = `<markdown>Hello</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>No edit pls.</coqcode></coqblock><input-area><markdown>HELLO</markdown></input-area><markdown>\n</markdown><hint title="optional"><markdown>## Header</markdown></hint><markdown>\n</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqcode>No edit pls.</coqcode></coqblock>`
    expect(translateMvToProsemirror(docString)).toBe(predict)
})

test("entire document2", () => {
    const docString = `# This is a header.

This is a paragraph. Paragraphs support inline LaTeX like $5+3=22$. Underneath you'll find a math display block.
$$
\operatorname{P} = \operatorname{NP}
$$
Headers can be changed to paragraphs and vice versa.

New \`inline math\` blocks can be created by pressing \`$\$$\` followed by a space and another \`$\$$\`.
New \`display math\` blocks can be created by inserting \`$\$\$$\` in the document followed by a space.

\`\`\`coq
From Coq Require Import List.
Import ListNotations.
\`\`\`
Above **and** below are Coq cells.

\`\`\`coq
(** * This is header*)
(** %\text{inline}%*)
(** $\text{display}$*)
Lemma rev_snoc_cons A :
  forall (x : A) (l : list A), rev (l ++ [x]) = x :: rev l.
Proof.
  (** Use induction on \`l.\`*)
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.
\`\`\``
    const predict = `<markdown># This is a header.

This is a paragraph. Paragraphs support inline LaTeX like $5+3=22$. Underneath you'll find a math display block.
</markdown><math-display>
\operatorname{P} = \operatorname{NP}
</math-display><markdown>
Headers can be changed to paragraphs and vice versa.

New \`inline math\` blocks can be created by pressing \`$\$$\` followed by a space and another \`$\$$\`.
New \`display math\` blocks can be created by inserting \`$\$\$$\` in the document followed by a space.
</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite="newLine"><coqcode>From Coq Require Import List.
Import ListNotations.</coqcode></coqblock><markdown>Above **and** below are Coq cells.
</markdown><coqblock prePreWhite="newLine" prePostWhite="newLine" postPreWhite="newLine" postPostWhite=""><coqdoc preWhite="" postWhite="newLine"><coqdown>* This is header</coqdown></coqdoc><coqdoc preWhite="" postWhite="newLine"><coqdown>%\text{inline}%</coqdown></coqdoc><coqdoc preWhite="" postWhite="newLine"><math-display>\text{display}</math-display></coqdoc><coqcode>Lemma rev_snoc_cons A :
  forall (x : A) (l : list A), rev (l ++ [x]) = x :: rev l.
Proof.
  (** Use induction on \`l.\`*)
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.</coqcode></coqblock>`
    expect(translateMvToProsemirror(docString)).toBe(predict)

})
