/// <reference types="cypress" />

import { MessageType } from "../../shared";
import { setupTest } from "./util";

const edits = [];
const initialDocument = "# Title\n```coq\nDefinition foo := 42.\n```\n";

const callbacks = {
    [MessageType.lineNumbers]: (data: { linenumbers: number[]; }) => {
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
    // CodeMirror Editor should exist
    cy.get('.cm-content').should("exist");
    // The line number gutter should not exist
    cy.get('.cm-gutter').should("not.exist");
    cy.window().then((win) => {
        win.postMessage({
            type: MessageType.setShowLineNumbers,
            body: true
        });
    });
    cy.wait(1);
    cy.get('.cm-gutter').should("exist");
    // Third line contains the coq code
    cy.get('.cm-gutter').should("contain", "3");
    cy.window().then((win) => {
        win.postMessage({
            type: MessageType.setShowLineNumbers,
            body: false
        });
    });
    cy.get('.cm-gutter').should("not.exist");
  });
})