/// <reference types="cypress" />
import { MessageType } from "../../shared";
import { setupTest } from "./util";

const edits = [];
const startingDocument: string = "# Title\n```coq\nDefinition foo := 42.\n```\n";

describe('Basic tests', () => {
  beforeEach(() => {
    setupTest(startingDocument, edits);
  })

  it('Editor opens, contains all parts and displays file', () => {
    // Editor is visible
    cy.get("#editor").should("be.visible");
    // Menubar is not visible by default
    cy.get(".menubar").should("not.be.visible");
    
    // Progress bar is visible
    // TODO: Progress bar only appears after clicking in the editor?
    // cy.get(".progress-bar").should("be.visible");
    
    // Editor should have a H1 (markdown header) and a .cm-content (coq code)
    cy.get("#editor h1").should("be.visible");
    cy.get("#editor .cm-content").should("be.visible");

    // Teacher mode is disabled, we should not be able to interact with 
    // the markdown or coq code
    cy.get("#editor h1").click(); 
    // Should **not** have changed the H1 into markdown editor
    cy.get("#editor h1").should("be.visible");

    // TODO: This also immediately opens the markdown editor for the H1
    cy.window().then((win) => { win.postMessage({type: MessageType.teacher, body: true}) });
    // now that we are in teacher mode the menubar should be visible
    cy.get(".menubar").should("be.visible");
    cy.get("coqblock > .cm-editor > .cm-scroller > .cm-content").click(); // to reset h1
    cy.get("#editor h1").should("be.visible");
    cy.get("#editor h1").click();
    cy.get(".markdown-view").should("be.visible");
  });

  it("Make basic edits to md and coq", () => {
    cy.window().then((win) => { win.postMessage({type: MessageType.teacher, body: true}) });
    cy.get(".markdown-view").type("\n## Hello World");
    cy.get(".markdown-view").should("contain.text", "Hello World");
    cy.nthCode(0).click(); // to reset h1
    cy.get("H2").should("exist");

    // We record edits in the 'edits' global variable
    //   this way we can check properties of the edits here
    cy.wrap(edits).then((edits) => {
      expect(edits.length).to.equal(15);

      // expect edits startInFile to be in increasing order
      expect(edits).to.satisfy((edits) => 
        edits.every((edit, i, arr) => 
          // startInFile equals endInFile (insertions)
          edit.startInFile === edit.endInFile  
          && 
          // startInFile's are in increasing order (consecutive)
          (i === 0 || arr[i-1].startInFile < edit.startInFile)
        )
      );

      // Flatten the edits finalText into one string
      const insertedText = edits.map(e => e.finalText).join("");
      expect(insertedText).to.equal("\n## Hello World");
    });

  });
})