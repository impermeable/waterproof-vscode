import { Position, TextDocument, Range, OutputChannel, languages, workspace, Disposable, window, DiagnosticSeverity } from "vscode";
import { DocumentSymbol, DocumentSymbolParams, DocumentSymbolRequest, LogTraceNotification, SymbolInformation } from "vscode-languageclient";
import { SentenceManager } from "./sentenceManager";
import { IFileProgressComponent } from "../components";
import { WebviewManager } from "../webviewManager";
import { qualifiedSettingName, WaterproofConfigHelper, WaterproofSetting, WaterproofLogger as wpl } from "../helpers";

import { LanguageClient as NodeLanguageClient } from "vscode-languageclient/node"
import { LanguageClient as BrowserLanguageClient } from "vscode-languageclient/browser"
import { InputAreaStatus, OffsetDiagnostic, Severity, SimpleProgressParams, WaterproofCompletion } from "@impermeable/waterproof-editor";
import { convertToSimple, FileProgressParams } from "./requestTypes";
import { MessageType } from "../../shared";
import { WpDiagnostic } from "./clientTypes";
import { GoalAnswer, GoalRequest } from "../../lib/types";

function vscodeSeverityToWaterproof(severity: DiagnosticSeverity): Severity {
    switch (severity) {
        case DiagnosticSeverity.Error: return Severity.Error;
        case DiagnosticSeverity.Warning: return Severity.Warning;
        case DiagnosticSeverity.Information: return Severity.Information;
        case DiagnosticSeverity.Hint: return Severity.Hint;
    }
}

function wasCanceledByServer(reason: unknown): boolean {
    return !!reason
        && typeof reason === "object"
        && "message" in reason
        && reason.message === "Request got old in server";  // or: code == -32802
}

// alternatively, this could be defined as `FeatureClient<Middleware, LanguageClientOptions>`
type LanguageClient = NodeLanguageClient | BrowserLanguageClient

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}

export abstract class LspClient<GoalRequestT extends GoalRequest, GoalAnswerT extends GoalAnswer> implements TimeoutDisposable {
    /**
     * The underlying VS Code language client.
     */
    readonly client: LanguageClient

    /**
     * Language identifier of this client, e.g. 'rocq' or 'lean4'
     */
    readonly language: string | undefined;

    /**
     * Resources that must be released upon disposal of this client.
     */
    readonly disposables: Disposable[] = [];

    detailedErrors: boolean = false;

    /**
     * The currently active document.
     * Only the `WebviewManager` should change this.
     */
    activeDocument: TextDocument | undefined;

    /**
     * The position of the text cursor in the active document.
     * Only the `WebviewManager` should change this.
     */
    activeCursorPosition: Position | undefined;

    /**
     * The object that keeps track of the (end) positions of the sentences in `activeDocument`.
     */
    readonly sentenceManager: SentenceManager;
    protected readonly fileProgressComponents: IFileProgressComponent[] = [];

    readonly lspOutputChannel: OutputChannel;

    webviewManager: WebviewManager | undefined;

    /**
     * Whether we are using viewport based checking.
     */
    readonly viewPortBasedChecking: boolean = !WaterproofConfigHelper.get(WaterproofSetting.ContinuousChecking);
    /**
     * The range of the current viewport.
     */
    viewPortRange: Range | undefined = undefined;

    /*
     * Constructs a Waterproof language client.
     */
    constructor(client: LanguageClient) {
        this.client = client;
        this.sentenceManager = new SentenceManager();

        // forward progress notifications to editor
        this.fileProgressComponents.push({
            dispose() { /* noop */ },
            onProgress: params => {
                const document = this.activeDocument;
                if (!document) return;
                const body: SimpleProgressParams = {
                    numberOfLines:  document.lineCount,
                    progress:       params.processing.map(convertToSimple)
                };
                this.webviewManager!.postAndCacheMessage(
                    document,
                    { type: MessageType.progress, body }
                );
            },
        });

        // deduce (end) positions of sentences from progress notifications
        this.fileProgressComponents.push(this.sentenceManager);
        const diagnosticsCollection = languages.createDiagnosticCollection(this.language);

        // Set detailedErrors to the value of the `Waterproof.detailedErrorsMode` setting.
        this.detailedErrors = WaterproofConfigHelper.get(WaterproofSetting.DetailedErrorsMode);
        // Update `detailedErrors` when the setting changes.
        this.disposables.push(workspace.onDidChangeConfiguration(e => {
            if (e.affectsConfiguration(qualifiedSettingName(WaterproofSetting.DetailedErrorsMode))) {
                this.detailedErrors = WaterproofConfigHelper.get(WaterproofSetting.DetailedErrorsMode);
            }

            // When the LogDebugStatements setting changes we update the logDebug boolean in the WaterproofLogger class.
            if (e.affectsConfiguration(qualifiedSettingName(WaterproofSetting.LogDebugStatements))) {
                wpl.logDebug = WaterproofConfigHelper.get(WaterproofSetting.LogDebugStatements);
            }
        }));

        // send diagnostics to editor (for squiggly lines)
        this.client.middleware.handleDiagnostics = (uri, diagnostics_) => {
            // Note: Here we typecast diagnostics_ to WpDiagnostic[], the new type includes the custom data field
            //      added by coq-lsp required for the line long error mode.
            if (!this.detailedErrors) {
                const diagnostics = (diagnostics_ as WpDiagnostic[]);
                diagnosticsCollection.set(uri, diagnostics.map(d => {
                    const start = d.data?.sentenceRange?.start ?? d.range.start;
                    const end = d.data?.sentenceRange?.end ?? d.range.end;
                    return {
                        message: d.message,
                        severity: d.severity,
                        range: new Range(start, end),
                    };
                }));
            } else {
                diagnosticsCollection.set(uri, diagnostics_);
            }
        };

        this.disposables.push(languages.onDidChangeDiagnostics(e => {
            if (this.activeDocument === undefined) return;
            // Comparing the uris (by doing uris.includes(this.activeDocument.uri)) does not seem to achieve
            // the same result.
            if (e.uris.map(uri => uri.path).includes(this.activeDocument.uri.path)) {
                this.processDiagnostics();
            }
        }));

        this.lspOutputChannel = window.createOutputChannel("Waterproof LSP Events (After Initialization)");

        // send proof statuses to editor when document checking is done
        this.disposables.push(this.client.onNotification(LogTraceNotification.type, params => {
            // Print `params.message` to custom lsp output channel
            this.lspOutputChannel.appendLine(params.message);

            if (params.message.includes("document fully checked")) {
                this.onCheckingCompleted();
            }
        }));
    }

    protected onFileProgress(params: FileProgressParams): void {
        // convert LSP range to VSC range
        params.processing.forEach((fp): void => {
            fp.range = this.client.protocol2CodeConverter.asRange(fp.range)
        });
        // notify each component
        this.fileProgressComponents.forEach(c => c.onProgress(params));
    }


    // Does this async do anything?
    protected async processDiagnostics() {
        const document = this.activeDocument;
        if (!document) return;

        const diagnostics = languages.getDiagnostics(document.uri);

        const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map(d => {
            return {
                message:        d.message,
                severity:       vscodeSeverityToWaterproof(d.severity),
                startOffset:    document.offsetAt(d.range.start),
                endOffset:      document.offsetAt(d.range.end)
            };
        });
        this.webviewManager!.postAndCacheMessage(document, {
            type: MessageType.diagnostics,
            body: {positionedDiagnostics, version: document.version}
        });
    }

    protected async onCheckingCompleted(): Promise<void> {
        // ensure there is an active document
        const document = this.activeDocument;
        if (!document) return;

        // send message to ProseMirror editor that checking is done
        // (in addition to LSP message that indicates last Markdown is still being processed)
        this.webviewManager!.postAndCacheMessage(
            document.uri.toString(),
            {
                type: MessageType.progress,
                body: { numberOfLines: document.lineCount, progress: [] }
            }
        );

        this.computeInputAreaStatus(document);
    }

    protected abstract determineProofStatus(document: TextDocument, inputArea: Range): Promise<InputAreaStatus>;

    protected abstract getInputAreas(document: TextDocument): Range[] | undefined;

    // This setTimeout creates a NodeJS.Timeout object, but in the browser it is just a number.
    computeInputAreaStatusTimer?: NodeJS.Timeout | number;

    protected async computeInputAreaStatus(document: TextDocument) {
        if (this.computeInputAreaStatusTimer) {
            clearTimeout(this.computeInputAreaStatusTimer);
        }
        // Computing where all the input areas are requires a fair bit of work,
        // so we add a debounce delay to this function to avoid recomputing on every keystroke.
        this.computeInputAreaStatusTimer = setTimeout(async () => {
            // get input areas based on tags
            const inputAreas = this.getInputAreas(document);
            if (!inputAreas) {
                throw new Error("Cannot check proof status; illegal input areas.");
            }

            // for each input area, check the proof status
            try {
                const statuses = await Promise.all(inputAreas.map(a => {
                    if (this.viewPortBasedChecking && this.viewPortRange && a.intersection(this.viewPortRange) === undefined) {
                        // This input area is outside of the range that has been checked and thus we can't determine its status
                        return Promise.resolve(InputAreaStatus.NotInView);
                    } else {
                        return this.determineProofStatus(document, a);
                    }
                }));

                // forward statuses to corresponding ProseMirror editor
                this.webviewManager!.postAndCacheMessage(document, {
                    type: MessageType.qedStatus,
                    body: statuses
                });
            } catch (reason) {
                if (wasCanceledByServer(reason)) return;  // we've likely already sent new requests
                console.log("[computeInputAreaStatus] The catch block caught an error that we don't classify as 'cancelled by server':", reason);
            }
        }, 250);
    }

    /**
     * Registers handlers (for, e.g., file progress notifications, which need to be forwarded to the
     * editor) and starts client.
     */
    startWithHandlers(webviewManager: WebviewManager): Promise<void> {
        this.webviewManager = webviewManager;

        // after every document change, request symbols and send completions to the editor
        this.disposables.push(workspace.onDidChangeTextDocument(event => {
            if (webviewManager.has(event.document.uri.toString()))
                this.updateCompletions(event.document);
        }));

        return this.client.start();
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

    /**
     * Creates parameter object for a goals request.
     */
    abstract createGoalsRequestParameters(document: TextDocument, position: Position): GoalRequestT;

    /** Sends an LSP request with the specified parameters to retrieve the goals. */
    abstract requestGoals(parameters: GoalRequestT): Promise<GoalAnswerT>;
    /** Sends an LSP request to retrieve the goals at `position` in the active document. */
    abstract requestGoals(position: Position): Promise<GoalAnswerT>;
    /** Sends an LSP request to retrieve the goals at the active cursor position. */
    abstract requestGoals(): Promise<GoalAnswerT>;

    /** Sends an LSP request to retrieve the symbols in the `activeDocument`. */
    async requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]> {
        // use active document if no document is given
        document ??= this.activeDocument;
        if (!document) {
            throw new Error("Cannot request symbols; there is no active document.");
        }

        // send "documentSymbol" request and wait for response
        const params: DocumentSymbolParams = {
            textDocument: {
                uri: document.uri.toString()
            }
        };
        const response = await this.client.sendRequest(DocumentSymbolRequest.type, params);

        // convert `response` to array of `DocumentSymbol` (if necessary) and return it
        if (!response) {
            console.error("Response to 'textDocument/documentSymbol' was `null`.");
            return [];
        } else if (response.length === 0 || "range" in response[0]) {
            return response as DocumentSymbol[];
        } else {
            return (response as SymbolInformation[]).map(s => ({
                name:           s.name,
                kind:           s.kind,
                tags:           s.tags,
                range:          s.location.range,
                selectionRange: s.location.range
            }));
        }
    }

    abstract sendViewportHint(document: TextDocument, start: number, end: number): Promise<void>;

    /**
     * Requests symbols and sends corresponding completions to the editor.
     */
    async updateCompletions(document: TextDocument): Promise<void> {
        if (!this.client.isRunning()) return;
        if (!this.webviewManager?.has(document)) {
            throw new Error("Cannot update completions; no ProseMirror webview is known for " + document.uri.toString());
        }

        // request symbols for `document`
        let symbols: DocumentSymbol[];
        try {
            symbols = await this.requestSymbols(document);
        } catch (reason) {
            if (wasCanceledByServer(reason)) return;  // we've likely already sent a new request
            throw reason;
        }

        // convert symbols to completions
        const completions: WaterproofCompletion[] = symbols.map(s => ({
            label:  s.name,
            detail: s.detail?.toLowerCase() ?? "",
            type:   "variable",
            template: s.name
        }));

        // send completions to (all code blocks in) the document's editor (not cached!)
        this.webviewManager.postMessage(document.uri.toString(), {
            type: MessageType.setAutocomplete,
            body: completions
        });
    }



    dispose(timeout?: number): Promise<void> {
        this.fileProgressComponents.forEach(c => c.dispose());
        this.disposables.forEach(d => d.dispose());
        return this.client.dispose(timeout);
    }
}
