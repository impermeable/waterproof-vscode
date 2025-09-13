/// <reference types="cypress" />
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { Message, MessageType } from "../../shared/Messages";

const edits = [];

const diagMessage = "     = 6\n     : nat";

const messages: Array<Message> = [
    {
        "type": MessageType.diagnostics,
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
        "type": MessageType.progress,
        "body": {
            "numberOfLines": 5,
            "progress": []
        }
    },
    {
        "type": MessageType.qedStatus,
        "body": [
          InputAreaStatus.Invalid
        ]
    },
    {
        "type": MessageType.diagnostics,
        "body": {
            "positionedDiagnostics": [
                {
                    "message": diagMessage,
                    "severity": 2,
                    "startOffset": 20,
                    "endOffset": 34
                }
            ],
            "version": 1
        }
    },
    {
        "type": MessageType.teacher,
        "body": true
    },
    {
        "type": MessageType.lineNumbers,
        "body": {
            "linenumbers": [
                2
            ],
            "version": 1
        }
    },
    {
        "type": MessageType.setAutocomplete,
        "body": []
    }
];

describe('TestingTest', () => {
  beforeEach(() => {
    cy.visit("../../__test_harness/index.html", {
      onBeforeLoad: (window) => {
        // Supply a 'fake' acquireVsCodeApi function
        // @ts-expect-error Okay for test purposes
        window.acquireVsCodeApi = function () {
          return {
            postMessage: (msg: Message) => {
              if (msg.type === MessageType.ready) {
                window.postMessage({
                    "type": MessageType.init,
                    "body": {
                        "value": "<input-area>\n```coq\nCompute 3 + 3.\n```\n</input-area>",
                        "format": "MarkdownV",
                        "version": 1
                    }
                });

                for (const message of messages) {
                  window.postMessage(message);
                }

              } else if (msg.type === MessageType.docChange) {
                // @ts-expect-error Okay for test purposes
                edits.push(msg.body);
              }
            }
          }
        }
      }
    });
  });

  it("Displays Info Message", () => {
    cy.get('.cm-lintRange.cm-lintRange-info').click().trigger('mouseover');
    cy.get('.cm-diagnostic').as("diag").should('be.visible').should('contain.text', diagMessage);
  });

  it("Displays the error box underneath", () => {
    cy.get('.cm-lintRange.cm-lintRange-info').click().trigger('mouseover');
    // Make sure we do have an input area
    cy.get("waterproofinput").should("exist");
    cy.get("waterproofinput").get('.cm-diagnostic').as("diag").should('be.visible').should('contain.text', diagMessage);
  });
})