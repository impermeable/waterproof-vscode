const edits = [];

describe('Input area', () => {
  beforeEach(() => {
    cy.visit("../../__test_harness/index.html", {
      onBeforeLoad: (window) => {
        // Supply a 'fake' acquireVsCodeApi function
        window.acquireVsCodeApi = function () {
          return {
            postMessage: (msg) => {
              if (msg.type === "ready") {
                window.postMessage({
                  type:"init",
                  body: {
                    value: "# Title\n<input-area>\n```coq\nDefinition foo := 42.\n```\n</input-area>\n",
                    format: "MarkdownV",
                    version: 1,
                  }
                });
              } else if (msg.type === "docChange") {
                edits.push(msg.body);
              }
            }
          }
        }
      }
    });
  });

  it("Basic input area functionality", () => {
    // We should have an input area in the document.
    cy.get("input-area").should("exist");
    
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
            for (let button of buttons) {
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