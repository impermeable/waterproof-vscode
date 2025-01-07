const messages = [
    {
        "type": "diagnostics",
        "body": {
            "positionedDiagnostics": [
                {
                    "message": "     = 6\n     : nat",
                    "severity": 2,
                    "startOffset": 20,
                    "endOffset": 34
                }
            ],
            "version": 1
        }
    },
    {
        "type": "progress",
        "body": {
            "numberOfLines": 5,
            "progress": []
        }
    },
    {
        "type": "qed",
        "body": [
            "invalid"
        ]
    },
    {
        "type": "diagnostics",
        "body": {
            "positionedDiagnostics": [
                {
                    "message": "     = 6\n     : nat",
                    "severity": 2,
                    "startOffset": 20,
                    "endOffset": 34
                }
            ],
            "version": 1
        }
    },
    {
        "type": "toggleTeacherMode",
        "body": true
    },
    {
        "type": "lineNumbers",
        "body": {
            "linenumbers": [
                2
            ],
            "version": 1
        }
    },
    {
        "type": "autocomplete",
        "body": []
    }
];
const edits = [];

describe('TestingTest', () => {
  beforeEach(() => {
    cy.visit("../../__test_harness/index.html", {
      onBeforeLoad: (window) => {
        // Supply a 'fake' acquireVsCodeApi function
        window.acquireVsCodeApi = function () {
          return {
            postMessage: (msg) => {
              if (msg.type === "ready") {
                window.postMessage({
                    "type": "init",
                    "body": {
                        "value": "<input-area>\n```coq\nCompute 3 + 3.\n```\n</input-area>",
                        "format": "MarkdownV",
                        "version": 1
                    }
                });

                for (const message of messages) {
                  window.postMessage(message);
                }
                
              } else if (msg.type === "docChange") {
                edits.push(msg.body);
              }
            }
          }
        }
      }
    });
  });

  it("Displays Info Message", () => {
    cy.get('.cm-lintRange').click().trigger('mouseover');
    cy.get('.cm-diagnostic').as("diag").should('be.visible').should('contain.text', '= 6');

  });
})