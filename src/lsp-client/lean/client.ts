import { LeanGoalAnswer, LeanGoalRequest } from "../../../lib/types";
import { LspClient } from "../client";
import { CancellationTokenSource, EventEmitter, Position, TextDocument, Disposable, Range, OutputChannel } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { FileProgressParams } from "../requestTypes";
import { leanFileProgressNotificationType, leanGoalRequestType, LeanPublishDiagnosticsParams } from "./requestTypes";
import { WaterproofConfigHelper, WaterproofLogger as wpl, WaterproofSetting } from "../../helpers";
import { LanguageClientProvider, WpDiagnostic } from "../clientTypes";
import { WebviewManager } from "../../webviewManager";
import { findOccurrences } from "../qedStatus";
import { InputAreaStatus, OffsetSemanticToken, SemanticTokenType } from "@impermeable/waterproof-editor";
import { ServerStoppedReason } from "@leanprover/infoview-api";
import { DidChangeTextDocumentParams, DidCloseTextDocumentParams, SemanticTokensRegistrationType } from "vscode-languageclient";
import { MessageType } from "../../../shared";

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
    language = "lean4";

    private semanticTokenTimer?: NodeJS.Timeout | number;

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
        if (this.activeDocument?.uri.toString() === progress.textDocument.uri) {
            this.computeInputAreaStatus(this.activeDocument);
            this.requestSemanticTokensDebounced(this.activeDocument);
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

    private requestSemanticTokensDebounced(document: TextDocument) {
        if (this.semanticTokenTimer) {
            clearTimeout(this.semanticTokenTimer);
        }
        this.semanticTokenTimer = setTimeout(() => {
            this.requestAndForwardSemanticTokens(document).catch(err => {
                wpl.debug(`Semantic token request failed: ${err}`)
        });
        }, 300);
    }

    private async requestAndForwardSemanticTokens(document: TextDocument): Promise<void> {
        if (!this.client.isRunning() || !this.webviewManager) return;

        const feature = this.client.getFeature(SemanticTokensRegistrationType.method);
        if (!feature) return;

        const provider = feature.getProvider(document);
        if (!provider?.full) return;

        const tokens = await Promise.resolve(provider.full.provideDocumentSemanticTokens(
            document,
            new CancellationTokenSource().token
        )).catch(() => undefined);

        if (!tokens?.data?.length) return;

        const tokenLegend = this.client.initializeResult?.capabilities.semanticTokensProvider?.legend;
        if (!tokenLegend) return;

        const offsetTokens: Array<OffsetSemanticToken> = LeanLspClient.decodeLspTokens(tokens.data).flatMap(t => {
            const tokenType = LeanLspClient.mapLspTokenType(tokenLegend.tokenTypes[t.tokenTypeIndex]);
            if (tokenType === undefined) return [];

            const startOffset = document.offsetAt(new Position(t.line, t.char));
            return [{
                startOffset,
                endOffset: startOffset + t.length,
                type: tokenType,
            }];
        });

        this.webviewManager.postMessage(document.uri.toString(), {
            type: MessageType.semanticTokens,
            body: {tokens: offsetTokens},
        });
    };

    // TODO increase code quality
    private static decodeLspTokens(data: Uint32Array): Array<{ line: number; char: number; length: number; tokenTypeIndex: number }> {
        const tokens = [];
        let line = 0;
        let char = 0;
        for (let i = 0; i < data.length; i += 5) {
            const deltaLine = data[i];
            const deltaStartChar = data[i + 1];
            if (deltaLine > 0) {
                line += deltaLine;
                char = deltaStartChar;
            } else {
                char += deltaStartChar;
            }
            tokens.push({
                line,
                char,
                length: data[i + 2],
                tokenTypeIndex: data[i + 3],
                // data[i + 4] is tokenModifiers (unused)
            });
        }
        return tokens;
    }

    private static mapLspTokenType(lspType: string): SemanticTokenType | undefined {
        switch (lspType) {
            case "keyword":
                return SemanticTokenType.Keyword;
            case "variable":
                return SemanticTokenType.Variable;
            case "property":
                return SemanticTokenType.Property;
            case "function":
                return SemanticTokenType.Function;
            default:
                return undefined;
        }
    }
}
