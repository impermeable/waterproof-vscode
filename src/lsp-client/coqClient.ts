import { Position, Range, TextDocument } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageclient";

import { CoqGoalAnswer, CoqGoalRequest, CoqServerStatusToServerStatus, GoalRequest, PpString } from "../../lib/types";
import { MessageType } from "../../shared";
import { coqFileProgressNotificationType, coqGoalRequestType, serverStatusNotificationType } from "./requestTypes";
import { WaterproofLogger as wpl } from "../helpers";
import { LspClient } from "./abstractLspClient";
import { LanguageClient } from "vscode-languageclient/node";

export class CoqLspClient extends LspClient<CoqGoalRequest, CoqGoalAnswer<PpString>> {
    language = "rocq";

    /**
     * Initializes the client.
     * @param args the arguments for the base `LanguageClient`
     */
    constructor(client: LanguageClient) {
        super(client);

        // call each file progress component when the server has processed a part
        this.disposables.push(this.client.onNotification(coqFileProgressNotificationType, params => {
            this.onFileProgress(params);
        }));

        this.disposables.push(this.client.onNotification(serverStatusNotificationType, params => {
            const document = this.activeDocument;
            if (!document) return;

            if (params.status === "Idle") {
                this.computeInputAreaStatus(document);
                // TODO: Maybe we should only process the diagnostics here?
                // I.e. do `this.processDiagnostics();` and not after every diagnostic change?
            }

            // Handle the server status notification
            this.webviewManager!.postMessage(document.uri.toString(), {
                    type: MessageType.serverStatus,
                    body: CoqServerStatusToServerStatus(params)
                }
            );
        }));
    }

    createGoalsRequestParameters(document: TextDocument, position: Position): CoqGoalRequest {
        return {
            textDocument: VersionedTextDocumentIdentifier.create(
                document.uri.toString(),
                document.version
            ),
            position: {
                line:      position.line,
                character: position.character
            }
        };
    }

    async requestGoals(params?: GoalRequest | Position): Promise<CoqGoalAnswer<PpString>> {
        if (!params || "line" in params) {  // if `params` is not a `GoalRequest` ...
            params ??= this.activeCursorPosition;
            if (!this.activeDocument || !params) {
                throw new Error("Cannot request goals; there is no active document and/or cursor position.");
            }
            params = this.createGoalsRequestParameters(this.activeDocument, params);
        }
        wpl.debug(`Sending request for goals with params: ${JSON.stringify(params)}`);
        return this.client.sendRequest(coqGoalRequestType, params);
    }

    async sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
        if (!this.client.isRunning()) return;
        const startPos = document.positionAt(start);
        let endPos = document.positionAt(end);
        // Compute end of document position, use that if we're close
        const endOfDocument = document.positionAt(document.getText().length);
        if (endOfDocument.line - endPos.line < 20) {
            endPos = endOfDocument;
        }

        const requestBody = {
            'textDocument':  VersionedTextDocumentIdentifier.create(
                document.uri.toString(),
                document.version
            ),
            'range': {
                start: {
                    line: startPos.line,
                    character: startPos.character
                },
                end: {
                    line: endPos.line,
                    character: endPos.character
                }
            }
        };

        // Save the range for which the document has been checked
        this.viewPortRange = new Range(startPos, endPos);
        await this.client.sendNotification("coq/viewRange", requestBody);
    }
}
