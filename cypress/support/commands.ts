/// <reference types="cypress" />

Cypress.Commands.add("inputAreas", () => {
    cy.get("input-area")
});

Cypress.Commands.add("nthInputArea", (n) => {
    cy.get("input-area").eq(n)
});

Cypress.Commands.add("coqCode", () => {
    cy.get('coqblock > .cm-editor > .cm-scroller > .cm-content')
});

Cypress.Commands.add("nthCoqCode", (n) => {
    cy.get('coqblock > .cm-editor > .cm-scroller > .cm-content').eq(n)
});

// TODO: Fix this
// eslint-disable-next-line @typescript-eslint/no-namespace
declare namespace Cypress {
    interface Chainable {
      /** Command to find all Waterproof input-areas. */ 
      inputAreas : () => Chainable<Element>
      /** Command to find the nth Waterproof input-area */
      nthInputArea : (n : number) => Chainable<Element>
      /** Command to find all Waterproof coq code blocks (CodeMirror instances). */ 
      coqCode : () => Chainable<Element>
      /** Command to find the nth Waterproof coq code block (CodeMirror instance). */
      nthCoqCode : (n: number) => Chainable<Element>
    }
  }
