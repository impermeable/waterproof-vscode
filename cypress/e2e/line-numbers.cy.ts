/// <reference types="cypress" />

import { MessageType } from "../../shared";
import { setupTest } from "./util";

const edits = [];
const initialDocument = "# Title\n<input-area>\n```coq\nDefinition foo := 42.\n```\n</input-area>\n";

const callbacks = {
    [MessageType.lineNumbers]: (data: any) => {
        // convert the zero based offset in `data.linenumbers` to line numbers.
        const lineNumbers = data.linenumbers.map((n: number) => 
            initialDocument.substring(0, n).split("\n").length - 1);

        cy.window().then((win) => {
            win.postMessage({
                type: MessageType.lineNumbers,
                body: {
                    linenumbers: lineNumbers,
                    version: 1,
                }
            })
        
        });
    }
}

describe('Line numbers', () => {
  beforeEach(() => { setupTest(initialDocument, edits, callbacks); });

  it("Toggle display of line numbers", () => {
    cy.get('.cm-content').should("exist");
    cy.get('.cm-gutter').should("not.exist");
    cy.window().then((win) => {
        win.postMessage({
            type: MessageType.setShowLineNumbers,
            body: true
        });
    });
    cy.wait(1);
    cy.get('.cm-gutter').should("exist");
    cy.get('.cm-gutter').should("contain", "4");
    cy.window().then((win) => {
        win.postMessage({
            type: MessageType.setShowLineNumbers,
            body: false
        });
    });
    cy.get('.cm-gutter').should("not.exist");
  });
})