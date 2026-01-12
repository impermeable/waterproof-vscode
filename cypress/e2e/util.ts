/// <reference types="cypress" />
import { DocChange, WrappingDocChange } from "@impermeable/waterproof-editor";
import {Message, MessageType} from "../../shared/Messages";
/**
 * Sets up the test harness and initializes the editor after receiving the
 * ready message from the editor.
 * @param initialDocument The initial document to load in the editor.
 * @param edits Array where the `docChange` events will be stored.
 */
// eslint-disable-next-line @typescript-eslint/no-unsafe-function-type
export function setupTest(initialDocument: string, edits: (DocChange | WrappingDocChange)[], callbacks?: Partial<Record<MessageType, Function>> ) {
    cy.visit("../../__test_harness/index.html", {
        onBeforeLoad: (window) => {
            // Supply a 'fake' acquireVsCodeApi function
            // @ts-expect-error Okay for test purposes
            window.acquireVsCodeApi = function () {
                return {
                    postMessage: (msg: Message) => {
                        if (msg.type === MessageType.ready) {
                            window.postMessage({
                                type: MessageType.init,
                                body: {
                                    value: initialDocument,
                                    version: 1,
                                }
                            });
                        } else if (msg.type === MessageType.docChange) {
                            edits.push(msg.body);
                        } else {
                            if (callbacks) {
                                const callback = callbacks[msg.type];
                                if (callback !== undefined)
                                    //@ts-expect-error Fine in tests
                                    callback(msg.body);
                            }
                        }
                    }
                }
            }
        }
    });
}