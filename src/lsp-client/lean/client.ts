import { LeanGoalAnswer, LeanGoalRequest } from "../../../lib/types";
import { LspClient } from "../client";
import { EventEmitter, Position, TextDocument, Disposable, Range, OutputChannel } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { FileProgressParams } from "../requestTypes";
import { leanFileProgressNotificationType, leanGoalRequestType, LeanPublishDiagnosticsParams } from "./requestTypes";
import { WaterproofLogger as wpl } from "../../helpers";
import { LanguageClientProvider, WpDiagnostic } from "../clientTypes";
import { WebviewManager } from "../../webviewManager";
import { findOccurrences } from "../qedStatus";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { ServerStoppedReason } from "@leanprover/infoview-api";
import { DidChangeTextDocumentParams, DidCloseTextDocumentParams } from "vscode-languageclient";

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
    language = "lean4";

    constructor(clientProvider: LanguageClientProvider, channel: OutputChannel) {
        super(clientProvider, channel);

        // call each file progress component when the server has processed a part
        this.disposables.push(this.client.onNotification(leanFileProgressNotificationType, params => {
            this.onFileProgress(params);
        }));

        const hndl = this.client.middleware.handleDiagnostics;
        this.client.middleware.handleDiagnostics = (uri, diagnostics_, next) => {
            if (hndl) hndl(uri, diagnostics_, next);

            // diagnostics formatting for infoview
            const c2p = this.client.code2ProtocolConverter;
            const uri_ = c2p.asUri(uri);

            const diagnostics = diagnostics_ as WpDiagnostic[];
            const infoviewDiagnostics = diagnostics.map(d => ({
                ...c2p.asDiagnostic(d),
                ...(d.data?.sentenceRange
                    ? { range: { start: d.data.sentenceRange.start, end: d.data.sentenceRange.end } }
                    : {})
            }));

            this.diagnosticsEmitter.fire({ uri: uri_, diagnostics: infoviewDiagnostics });
        };
    }

    protected async onFileProgress(progress: FileProgressParams) {
        if (this.activeDocument?.uri.toString() === progress.textDocument.uri) {
            this.computeInputAreaStatus(this.activeDocument);
        }

        super.onFileProgress(progress);
    }

    createGoalsRequestParameters(document: TextDocument, position: Position): LeanGoalRequest {
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

    async requestGoals(params?: LeanGoalRequest | Position): Promise<LeanGoalAnswer> {
        if (!params || "line" in params) {  // if `params` is not a `GoalRequest` ...
            params ??= this.activeCursorPosition;
            if (!this.activeDocument || !params) {
                throw new Error("Cannot request goals; there is no active document and/or cursor position.");
            }
            params = this.createGoalsRequestParameters(this.activeDocument, params);
        }
        wpl.debug(`Sending request for goals with params: ${JSON.stringify(params)}`);
        return this.client.sendRequest(leanGoalRequestType, params);
    }

    async sendViewportHint(_document: TextDocument, _start: number, _end: number): Promise<void> {
        // this is not currently used or supported by Lean
    }

    async startWithHandlers(webviewManager: WebviewManager): Promise<string[]> {
        const lang = await super.startWithHandlers(webviewManager);

        // Allows for any custom notifications to be handled by
        // forwarding to a custom notification emitter

        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        const starHandler = (method: string, params_: any) => {
            this.customNotificationEmitter.fire({ method, params: params_ })
        };
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        this.client.onNotification(starHandler as any, () => { });
        return lang;
    }

    protected getInputAreas(document: TextDocument): Range[] | undefined {
        const content = document.getText();

        // find (positions of) opening and closings tags for input areas, and check that they're valid
        const openOffsets = findOccurrences(":::input\n", content);

        return openOffsets.map(openPos => {
            const closePos = content.indexOf(":::\n", openPos);
            return new Range(
                document.positionAt(openPos),
                document.positionAt(closePos),
            );
        });
    }

    protected async determineProofStatus(document: TextDocument, inputArea: Range): Promise<InputAreaStatus> {
        const content = document.getText();

        const nextQed = content.indexOf("\nQed\n", document.offsetAt(inputArea.start));
        const nextProof = content.indexOf("\nProof:\n", document.offsetAt(inputArea.start));

        if (nextProof && nextQed >= nextProof) {
            return InputAreaStatus.Invalid;
        }

        // request goals and return conclusion based on them
        const response = await this.requestGoals(this.createGoalsRequestParameters(document, inputArea.end.translate(0, 0)));

        return response?.goals.length ? InputAreaStatus.Incomplete : InputAreaStatus.Proven;
    }

    // Emitters for infoview
    private didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>();
    public didChange(cb: (params: DidChangeTextDocumentParams) => void): Disposable {
        return this.didChangeEmitter.event(cb);
    }

    private didCloseEmitter = new EventEmitter<DidCloseTextDocumentParams>();
    public didClose(cb: (params: DidCloseTextDocumentParams) => void): Disposable {
        return this.didCloseEmitter.event(cb);
    }

    private diagnosticsEmitter = new EventEmitter<LeanPublishDiagnosticsParams>();
    public diagnostics(cb: (params: LeanPublishDiagnosticsParams) => void): Disposable {
        return this.diagnosticsEmitter.event(cb);
    }

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    private customNotificationEmitter = new EventEmitter<{ method: string; params: any }>()

    /** Fires whenever a custom notification (i.e. one not defined in LSP) is received. */
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    public customNotification(cb: (params: any) => void): Disposable {
        return this.customNotificationEmitter.event(cb);
    }

    private clientStoppedEmitter = new EventEmitter<ServerStoppedReason>();
    public clientStopped = this.clientStoppedEmitter.event;

    async dispose(timeout?: number): Promise<void> {
        await super.dispose(timeout);
        this.clientStoppedEmitter.fire({message: 'Lean server has stopped', reason: ''});
    }
}
