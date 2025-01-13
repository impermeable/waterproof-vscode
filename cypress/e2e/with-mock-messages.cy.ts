/// <reference types="cypress" />
import { Message, MessageType } from "../../shared/Messages";

const edits: any[] = [];

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
            "invalid"
        ]
    },
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
        //@ts-ignore
        window.acquireVsCodeApi = function () {
          return {
            postMessage: (msg: Message) => {
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