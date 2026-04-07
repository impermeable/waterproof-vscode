import { LeanGoalAnswer, LeanGoalRequest } from "../../../lib/types";
import { LspClient } from "../client";
import { EventEmitter, Position, TextDocument, Disposable, Range, OutputChannel, Diagnostic, DiagnosticSeverity } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { FileProgressParams } from "../requestTypes";
import { leanFileProgressNotificationType, leanGoalRequestType, LeanPublishDiagnosticsParams } from "./requestTypes";
import { WaterproofConfigHelper, WaterproofLogger as wpl, WaterproofSetting } from "../../helpers";
import { LanguageClientProvider, WpDiagnostic } from "../clientTypes";
import { WebviewManager } from "../../webviewManager";
import { findOccurrences } from "../qedStatus";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { ServerStoppedReason } from "@leanprover/infoview-api";
import { DidChangeTextDocumentParams, DidCloseTextDocumentParams } from "vscode-languageclient";
import { FileProgressKind, MessageType } from "../../../shared";

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
    language = "lean4";

    /**
    * Whether the Lean server is still processing the document.
    * Used to avoid marking a proof as complete before checking has finished.
    */
    private isBusy: boolean = true; 

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

    async prelaunchChecks(): Promise<string[]> {
        const lakePath = WaterproofConfigHelper.get(WaterproofSetting.LakePath);
        if (!lakePath) {
            wpl.log("Lean prelaunch check failed: lakePath is empty.");
            return [];
        }

        const command = `${lakePath} --version`;
        const ok = await this.execReturnsOk(command);
        return ok ? [this.language] : [];
    }

    private async execReturnsOk(command: string): Promise<boolean> {
        wpl.log(`Running command: ${command}`);
        return new Promise(resolve => {
            // eslint-disable-next-line @typescript-eslint/no-require-imports
            const { exec } = require("child_process");
            exec(command, (err: { message?: string } | null) => {
                if (err) {
                    const message = err.message ?? "Unknown error";
                    wpl.log(`Lean prelaunch check failed: ${message}`);
                    resolve(false);
                } else {
                    resolve(true);
                }
            });
        });
    }

    protected async onFileProgress(progress: FileProgressParams) {

        // Call super first so LSP ranges are converted to VSCode Ranges before we store/use them.
        super.onFileProgress(progress);

        if (this.activeDocument?.uri.toString() === progress.textDocument.uri) {
            
            // --- busy-indicator (Lean edition) ---
            // Find the first processing range, where we want to add the busy-indicator to.
            const firstProcessing = progress.processing.find(
                p => p.kind === undefined || p.kind === FileProgressKind.Processing
            );
            if (firstProcessing && this.webviewManager) {
                this.isBusy = true;
                const { line, character } = firstProcessing.range.start;
                const from = this.activeDocument.offsetAt(new Position(line, character));
                const to   = this.activeDocument.offsetAt(new Position(
                    firstProcessing.range.end.line,
                    firstProcessing.range.end.character,
                ));

                // Send message to add the busy indicator
                this.webviewManager.postMessage(progress.textDocument.uri, {
                    type: MessageType.executionInfo,
                    body: { from, to },
                });
            } else {
                this.isBusy = false;
            }
            this.computeInputAreaStatus(this.activeDocument);
        }
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

    async requestGoals(params?: LeanGoalRequest | Position): Promise<LeanGoalAnswer | null> {
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

    async startWithHandlers(webviewManager: WebviewManager, allowedLanguages: string[]): Promise<string[]> {
        const lang = await super.startWithHandlers(webviewManager, allowedLanguages);

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

    protected async determineProofStatus(document: TextDocument, inputArea: Range, diags: Array<Diagnostic>, lowerBound: Position,): Promise<InputAreaStatus> {

        // If Lean hasn't finished processing up to the end of this input area, an empty goals
        // response simply means "not checked yet" rather than "proof complete".  Guard against
        // that to prevent the bar from turning green prematurely (e.g. while typing "We ap" or
        // when the proof has invalid syntax like "Help\n• Fix a : ℝ\n" without a closing Qed).
        if (this.isBusy) {
            return InputAreaStatus.Incorrect;
        }

        // Get diagnostics that intersect with the input area, and check if any of them are error-level.
        const diagsInArea = diags.filter(v => {
            const intersection = inputArea.intersection(v.range);
            return intersection !== undefined && !intersection.isEmpty;
        });

        // If there are any error-level diagnostics inside the input area, the proof is wrong.
        // This catches cases like an incomplete tactic keyword (e.g. just "We") which can make
        // Lean report empty goals at the query position while still being invalid.
        const hasErrorDiagnostic = diagsInArea.some(d => d.severity === DiagnosticSeverity.Error);
        if (hasErrorDiagnostic) {
            return InputAreaStatus.Incorrect;
        }
 
        // Request goals
        const goalsPosition = inputArea.end.translate(0, 0);
        
        const goalsParams = this.createGoalsRequestParameters(document, goalsPosition);
        const response = await this.requestGoals(goalsParams);

        if (!response) {
            return InputAreaStatus.Incorrect;
        }
        
        // return incorrect if there are still goals remaining
        if (response.goals.length > 0) return InputAreaStatus.Incorrect;

        // Goals are empty, proof looks complete, but check for sorry
        const SORRY_RE = /declaration uses 'sorry'/m;

        const hasSorry = diags.some(d =>
            d.range.start.isAfter(lowerBound) &&
            d.range.start.isBeforeOrEqual(inputArea.end) &&
            SORRY_RE.test(d.message)
        );
        return hasSorry ? InputAreaStatus.Invalid : InputAreaStatus.Correct;
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