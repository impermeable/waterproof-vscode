import { OutputChannel, Position, Range, TextDocument } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageclient";

import { CoqGoalAnswer, CoqGoalRequest, CoqServerStatusToServerStatus, GoalRequest, PpString } from "../../../lib/types";
import { MessageType } from "../../../shared";
import { coqFileProgressNotificationType, coqGoalRequestType, coqServerStatusNotificationType } from "./requestTypes";
import { WaterproofLogger as wpl } from "../../helpers";
import { LspClient } from "../client";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { findOccurrences, areInputAreasValid } from "../qedStatus";
import { LanguageClientProvider } from "../clientTypes";

export class CoqLspClient extends LspClient<CoqGoalRequest, CoqGoalAnswer<PpString>> {
    language = "rocq";

    /**
     * Initializes the client.
     * @param args the arguments for the base `LanguageClient`
     */
    constructor(clientProvider: LanguageClientProvider, channel: OutputChannel) {
        super(clientProvider, channel);

        // call each file progress component when the server has processed a part
        this.disposables.push(this.client.onNotification(coqFileProgressNotificationType, params => {
            this.onFileProgress(params);
        }));

        this.disposables.push(this.client.onNotification(coqServerStatusNotificationType, params => {
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

    protected getInputAreas(document: TextDocument): Range[] | undefined {
        const content = document.getText();

        // find (positions of) opening and closings tags for input areas, and check that they're valid
        const openOffsets = findOccurrences("<input-area>", content);
        const closeOffsets = findOccurrences("</input-area>", content);
        if (!areInputAreasValid(openOffsets, closeOffsets)) return undefined;

        // We know the length of this array in advance
        const inputAreas: Range[] = new Array(openOffsets.length);
        for (let i = 0; i < openOffsets.length; i++) {
            // Convert the open and close positions to ranges
            inputAreas[i] = new Range(
                document.positionAt(openOffsets[i]),
                document.positionAt(closeOffsets[i]),
            );
        }
        return inputAreas;
    }

    protected async determineProofStatus(document: TextDocument, inputArea: Range): Promise<InputAreaStatus> {
        // get the (end) position of the last line in the input area
        // funnily, it can be in a next input area, and we accept this
        const position = this.sentenceManager.getEndOfSentence(inputArea.end, true);
        if (!position) {
            // console.warn("qedStatus.ts : No sentence after input area");
            return InputAreaStatus.Invalid;
        }

        // check that last command is "Qed" (or return "invalid")
        // note that we don't allow, e.g., comments between "Qed" and "."
        const i = position.character - 4;
        if (i < 0 || document.lineAt(position).text.slice(i, i+4) !== "Qed.") {
            // console.warn("qedStatus.ts : Last sentence is not `Qed.`");
            return InputAreaStatus.Invalid;
        }

        // request goals and return conclusion based on them
        const response = await this.requestGoals(position.translate(0, -1));
        return ("error" in response) ? InputAreaStatus.Incomplete : InputAreaStatus.Proven;
    }

    /**
     * Returns the end position of the currently selected sentence, i.e., the Coq sentence in the
     * active document in which the text cursor is located. Only returns `undefined` if no sentences
     * are known.
     */
    getBeginningOfCurrentSentence(): Position | undefined {
        if (!this.activeCursorPosition) return undefined;
        return this.sentenceManager.getBeginningOfSentence(this.activeCursorPosition);
    }

    /**
     * Returns the beginning position of the currently selected sentence, i.e., the Coq sentence in the
     * active document in which the text cursor is located. Only returns `undefined` if no sentences
     * are known. This is really just the end position of the previous sentence.
     */
    getEndOfCurrentSentence(): Position | undefined {
        if (!this.activeCursorPosition) return undefined;
        return this.sentenceManager.getEndOfSentence(this.activeCursorPosition);
    }
}
