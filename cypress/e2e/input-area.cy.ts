/// <reference types="cypress" />

import { setupTest } from "./util";

const edits = [];
const initialDocument = "# Title\n<input-area>\n```coq\nDefinition foo := 42.\n```\n</input-area>\n";

describe('Input area', () => {
  beforeEach(() => { setupTest(initialDocument, edits); });

  it("Basic input area functionality", () => {
    // We should have an input area in the document.
    cy.inputAreas().should("exist");
    
    // Teacher mode disabled => we should not be able to edit
    //   the markdown
    cy.get("H1").click();
    cy.get("H1").should("exist");

    // The menubar buttons should be disabled when **not**
    //   in the input area.

    cy.get(".menubar .menubar-item").filter(":lt(6)")
        .invoke("attr", "disabled").should("exist");
    
    // The menubar buttons should be enabled when in the input area.
    cy.get(".cm-content").click();
    cy.get(".menubar .menubar-item").filter(":lt(6)").then((buttons) => {
        expect(buttons).to.satisfy((buttons) => {
            for (const button of buttons) {
                if (button.getAttribute("disabled") === "true") {
                    return false;
                }
            }
            return true;    
        });
    });

    // We should be able to type in the input area.
    cy.get(".cm-content").type("\nDefinition bar := 42.");
    cy.get(".cm-content").should("contain.text", "Definition bar := 42.");
  });
})