import { DiagnosticSeverity, Disposable, OutputChannel, Position, Range, TextDocument, languages, window, workspace } from "vscode";
import {
    DocumentSymbol, DocumentSymbolParams, DocumentSymbolRequest, FeatureClient,
    LanguageClientOptions,
    LogTraceNotification,
    Middleware,
    SymbolInformation,
    VersionedTextDocumentIdentifier
} from "vscode-languageclient";

import { CoqServerStatusToServerStatus, GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { MessageType } from "../../shared";
import { IFileProgressComponent } from "../components";
import { WebviewManager } from "../webviewManager";
import { ICoqLspClient, WpDiagnostic } from "./clientTypes";
import { determineProofStatus, getInputAreas } from "./qedStatus";
import { convertToSimple, fileProgressNotificationType, goalRequestType, serverStatusNotificationType } from "./requestTypes";
import { SentenceManager } from "./sentenceManager";
import { qualifiedSettingName, WaterproofConfigHelper, WaterproofSetting, WaterproofLogger as wpl } from "../helpers";
import { SimpleProgressParams, OffsetDiagnostic, Severity, WaterproofCompletion, InputAreaStatus } from "@impermeable/waterproof-editor";

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}

// Seems to be needed for the mixin class below
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type ClientConstructor = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & TimeoutDisposable;

function vscodeSeverityToWaterproof(severity: DiagnosticSeverity): Severity {
    switch (severity) {
        case DiagnosticSeverity.Error: return Severity.Error;
        case DiagnosticSeverity.Warning: return Severity.Warning;
        case DiagnosticSeverity.Information: return Severity.Information;
        case DiagnosticSeverity.Hint: return Severity.Hint;
    }
}

/**
 * The following function allows for a Mixin i.e. we can add the interface
 * CoqFeatures to arbitrary subclasses of BaseLanguageClient; that way extending
 * an object whose type is only known at runtime
 * @public
 */
export function CoqLspClient<T extends ClientConstructor>(Base: T) {
    return class extends Base implements ICoqLspClient {

        /** The resources that must be released when this extension is disposed of */
        readonly disposables: Disposable[] = [];

        detailedErrors: boolean = false;

        activeDocument: TextDocument | undefined;
        activeCursorPosition: Position | undefined;

        readonly sentenceManager: SentenceManager;
        readonly fileProgressComponents: IFileProgressComponent[] = [];

        readonly lspOutputChannel: OutputChannel;

        webviewManager: WebviewManager | undefined;

        // Whether we are using viewport based checking.
        readonly viewPortBasedChecking: boolean = !WaterproofConfigHelper.get(WaterproofSetting.ContinuousChecking);
        // The range of the current viewport.
        viewPortRange: Range | undefined = undefined;

        /**
         * Initializes the client.
         * @param args the arguments for the base `LanguageClient`
         */
        // Needed for the mixin class
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        constructor(...args: any[]) { 
            super(...args);
            this.sentenceManager = new SentenceManager();
            wpl.debug("CoqLspClient constructor");
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
            const diagnosticsCollection = languages.createDiagnosticCollection("rocq");
            
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
            this.middleware.handleDiagnostics = (uri, diagnostics_) => {
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

            // call each file progress component when the server has processed a part
            this.disposables.push(this.onNotification(fileProgressNotificationType, params => {
                // convert LSP range to VSC range
                params.processing.forEach(fp => { fp.range = this.protocol2CodeConverter.asRange(fp.range) });
                // notify each component
                this.fileProgressComponents.forEach(c => c.onProgress(params));
            }));

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
            this.disposables.push(this.onNotification(LogTraceNotification.type, params => {
                // Print `params.message` to custom lsp output channel
                this.lspOutputChannel.appendLine(params.message);
                
                if (params.message.includes("document fully checked")) {
                    this.onCheckingCompleted();
                }
            }));

            this.disposables.push(this.onNotification(serverStatusNotificationType, params => {
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

        // Does this async do anything? 
        async processDiagnostics() {
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

        async onCheckingCompleted(): Promise<void> {
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

        // This setTimeout creates a NodeJS.Timeout object, but in the browser it is just a number.
        computeInputAreaStatusTimer?: NodeJS.Timeout | number;

        async computeInputAreaStatus(document: TextDocument) {
            if (this.computeInputAreaStatusTimer) {
                clearTimeout(this.computeInputAreaStatusTimer);
            }
            // Computing where all the input areas are requires a fair bit of work,
            // so we add a debounce delay to this function to avoid recomputing on every keystroke.
            this.computeInputAreaStatusTimer = setTimeout(async () => {
                // get input areas based on tags
                const inputAreas = getInputAreas(document);
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
                                return determineProofStatus(this, document, a);
                            }
                        }
                    ));

                    // forward statuses to corresponding ProseMirror editor
                    this.webviewManager!.postAndCacheMessage(document, {
                        type: MessageType.qedStatus,
                        body: statuses
                    });
                } catch (reason) {
                    if (wasCanceledByServer(reason)) return;  // we've likely already sent new requests
                    console.log("[computeInputAreaStatus] The catch block caught an error that we don't classify as 'cancelled by server':", reason);
                }
            }, WaterproofConfigHelper.get(WaterproofSetting.DebounceTime));
        }

        startWithHandlers(webviewManager: WebviewManager): Promise<void> {
            this.webviewManager = webviewManager;

            // after every document change, request symbols and send completions to the editor
            this.disposables.push(workspace.onDidChangeTextDocument(event => {
                if (webviewManager.has(event.document.uri.toString()))
                    this.updateCompletions(event.document);
            }));

            return this.start();
        }

        getBeginningOfCurrentSentence(): Position | undefined {
            if (!this.activeCursorPosition) return undefined;
            return this.sentenceManager.getBeginningOfSentence(this.activeCursorPosition);
        }

        getEndOfCurrentSentence(): Position | undefined {
            if (!this.activeCursorPosition) return undefined;
            return this.sentenceManager.getEndOfSentence(this.activeCursorPosition);
        }

        createGoalsRequestParameters(document: TextDocument, position: Position): GoalRequest {
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

        async requestGoals(params?: GoalRequest | Position): Promise<GoalAnswer<PpString>> {
            if (!params || "line" in params) {  // if `params` is not a `GoalRequest` ...
                params ??= this.activeCursorPosition;
                if (!this.activeDocument || !params) {
                    throw new Error("Cannot request goals; there is no active document and/or cursor position.");
                }
                params = this.createGoalsRequestParameters(this.activeDocument, params);
            }
            wpl.debug(`Sending request for goals with params: ${JSON.stringify(params)}`);
            return this.sendRequest(goalRequestType, params);
        }

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
            const response = await this.sendRequest(DocumentSymbolRequest.type, params);

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

        async sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
            if (!this.isRunning()) return;
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
            await this.sendNotification("coq/viewRange", requestBody);
        }

        async updateCompletions(document: TextDocument): Promise<void> {
            if (!this.isRunning()) return;
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
            return super.dispose(timeout);
    }
}

function wasCanceledByServer(reason: unknown): boolean {
    return !!reason
        && typeof reason === "object"
        && "message" in reason
        && reason.message === "Request got old in server";  // or: code == -32802
}
}