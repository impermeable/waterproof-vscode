import { Completion } from "@codemirror/autocomplete";
import { Disposable, OutputChannel, Position, TextDocument, languages, window, workspace } from "vscode";
import {
    DocumentSymbol, DocumentSymbolParams, DocumentSymbolRequest, FeatureClient,
    LanguageClientOptions,
    LogTraceNotification,
    Middleware,
    SymbolInformation,
    VersionedTextDocumentIdentifier
} from "vscode-languageclient";

import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { MessageType, OffsetDiagnostic, InputAreaStatus, SimpleProgressParams } from "../../shared";
import { IFileProgressComponent } from "../components";
import { WebviewManager } from "../webviewManager";
import { ICoqLspClient, WpDiagnostic } from "./clientTypes";
import { determineProofStatus, getInputAreas } from "./qedStatus";
import { convertToSimple, fileProgressNotificationType, goalRequestType } from "./requestTypes";
import { SentenceManager } from "./sentenceManager";
import { WaterproofConfigHelper, WaterproofLogger as wpl } from "../helpers";

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}

// Seems to be needed for the mixin class below
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type ClientConstructor = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & TimeoutDisposable;

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
            const diagnosticsCollection = languages.createDiagnosticCollection("coq");
            
            // Set detailedErrors to the value of the `Waterproof.detailedErrorsMode` setting.
            this.detailedErrors = WaterproofConfigHelper.detailedErrors;
            // Update `detailedErrors` when the setting changes.
            this.disposables.push(workspace.onDidChangeConfiguration(e => {
                if (e.affectsConfiguration("waterproof.detailedErrorsMode")) {
                    this.detailedErrors = WaterproofConfigHelper.detailedErrors;
                }
            }));

            // send diagnostics to editor (for squiggly lines)
            this.middleware.handleDiagnostics = (uri, diagnostics_) => {
                diagnosticsCollection.set(uri, diagnostics_);

                // Note: Here we typecast diagnostics_ to WpDiagnostic[], the new type includes the custom data field 
                //      added by coq-lsp required for the detailed error mode.
                const diagnostics = (diagnostics_ as WpDiagnostic[]);
                const document = this.activeDocument;
                if (!document) return;
                const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map(d => {
                    if (this.detailedErrors) {
                        return {
                            message:        d.message,
                            severity:       d.severity,
                            startOffset:    document.offsetAt(d.range.start),
                            endOffset:      document.offsetAt(d.range.end)
                        };
                    } else {
                        if (d.data !== undefined && d.data.sentenceRange !== undefined) {
                            // Compute line-long start and end positions
                            const newStart = new Position(
                                d.data.sentenceRange.start.line,
                                d.data.sentenceRange.start.character
                            );
                            const newEnd = new Position(
                                d.data.sentenceRange.end.line,
                                d.data.sentenceRange.end.character
                            );
                            return {
                                message:        d.message,
                                severity:       d.severity,
                                startOffset:    document.offsetAt(newStart),
                                endOffset:      document.offsetAt(newEnd)
                            };
                        } else {
                            return {
                                message:        d.message,
                                severity:       d.severity,
                                startOffset:    document.offsetAt(d.range.start),
                                endOffset:      document.offsetAt(d.range.end)
                            };
                        }
                    }
                });
                this.webviewManager!.postAndCacheMessage(document, {
                    type: MessageType.diagnostics,
                    body: {positionedDiagnostics, version: document.version}
                });
            };

            // call each file progress component when the server has processed a part
            this.disposables.push(this.onNotification(fileProgressNotificationType, params => {
                // convert LSP range to VSC range
                params.processing.forEach(fp => { fp.range = this.protocol2CodeConverter.asRange(fp.range) });
                // notify each component
                this.fileProgressComponents.forEach(c => c.onProgress(params));
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

            // get input areas based on tags
            const inputAreas = getInputAreas(document);
            if (!inputAreas) {
                throw new Error("Cannot check proof status; illegal input areas.");
            }

            // for each input area, check the proof status
            let statuses: InputAreaStatus[];
            try {
                statuses = await Promise.all(inputAreas.map(a =>
                    determineProofStatus(this, document, a)
                ));
            } catch (reason) {
                if (wasCanceledByServer(reason)) return;  // we've likely already sent new requests
                throw reason;
            }

            // forward statuses to corresponding ProseMirror editor
            this.webviewManager!.postAndCacheMessage(document, {
                type: MessageType.qedStatus,
                body: statuses
            });
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
            wpl.debug(`Requesting goals with params: ${JSON.stringify(params)}`);
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
            const completions: Completion[] = symbols.map(s => ({
                label:  s.name,
                detail: s.detail?.toLowerCase(),
                type:   "variable"
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
}

function wasCanceledByServer(reason: unknown): boolean {
    return !!reason
        && typeof reason === "object"
        && "message" in reason
        && reason.message === "Request got old in server";  // or: code == -32802
}
