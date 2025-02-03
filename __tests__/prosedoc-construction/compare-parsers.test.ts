/**
 * @jest-environment jsdom
 */

/* eslint-disable no-useless-escape */
// Disable due to latex code in sample data

import { createProseMirrorDocument } from "../../editor/src/kroqed-editor/prosedoc-construction/construct-document";
import { FileFormat } from "../../shared";
import { FileTranslator } from "../../editor/src/kroqed-editor/translation"
import { TheSchema } from "../../editor/src/kroqed-editor/kroqed-schema";
import { DOMParser} from "prosemirror-model";
import { expect } from "@jest/globals";

const inputDocument = `#### Markdown content
$\int_2^3 x dx$
$$1028 + 23 = ?$$
Lol, empty coq block underneath.
\`\`\`coq
\`\`\`
\`\`\`coq
5<10.
Definition test := 1.
\`\`\`
<hint title="> 📦 Imports (click to open/close)">
\`\`\`coq
Require Import ZArith.
\`\`\`
</hint>
<input-area>
input area test
</input-area>
\`\`\`coq
(** * Coqdoc Header %2x^2 + 4 <1% *)
(* regular comment *)
Compute 5 + 10.
(** Some random text 
$\text{display math} $ *)
(** 
- Item 1
- Item 2 *)
\`\`\``;

test("createProseMirrorDocument", () => {
    const outputNode = createProseMirrorDocument(inputDocument, FileFormat.MarkdownV);
    const jsonOutput = outputNode.toJSON();

    const translator = new FileTranslator(FileFormat.MarkdownV);
    const translatedString = translator.toProsemirror(inputDocument);
    const div = document.createElement("div");
    div.innerHTML = translatedString;
    const oldOutputNode = DOMParser.fromSchema(TheSchema).parse(div);
    const oldJsonOutput = oldOutputNode.toJSON();

    expect(jsonOutput).toMatchObject(oldJsonOutput);
});