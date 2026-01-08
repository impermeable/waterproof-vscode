import { LanguageClient } from "vscode-languageclient/node";
import { LeanGoalAnswer, LeanGoalRequest } from "../../lib/types";
import { LspClient } from "./abstractLspClient";
import { EventEmitter, Position, TextDocument, Disposable } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { leanFileProgressNotificationType, leanGoalRequestType } from "./requestTypes";
import { WaterproofLogger as wpl } from "../helpers";
import { WpDiagnostic } from "./clientTypes";
import { WebviewManager } from "../webviewManager";

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
    language = "lean4";

    constructor(client: LanguageClient) {
        super(client);

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
        }

        // TODO: subscribe to server status notifications?
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
        // FIXME: remove this method (from the parent class as well) as Lean
        //        does not seem to support incremental verification based on
        //        viewport range
    }

    async startWithHandlers(webviewManager: WebviewManager): Promise<void> {
        await super.startWithHandlers(webviewManager);

        // Add special handling of custom notifications
        const starHandler = (method: string, params_: any) => {
          this.customNotificationEmitter.fire({ method, params: params_ })
        };
        this.client.onNotification(starHandler as any, () => { });
    }

    // Emitters for infoview
    private didChangeEmitter = new EventEmitter<any>();
    public didChange(cb: (params: any) => void): Disposable {
        return this.didChangeEmitter.event(cb);
    }

    private didCloseEmitter = new EventEmitter<any>();
    public didClose(cb: (params: any) => void): Disposable {
        return this.didCloseEmitter.event(cb);
    }

    private diagnosticsEmitter = new EventEmitter<any>();
    public diagnostics(cb: (params: any) => void): Disposable {
        return this.diagnosticsEmitter.event(cb);
    }

    private customNotificationEmitter = new EventEmitter<{ method: string; params: any }>()

    /** Fires whenever a custom notification (i.e. one not defined in LSP) is received. */
    public customNotification(cb: (params: any) => void): Disposable {
        return this.customNotificationEmitter.event(cb);
    }
}
