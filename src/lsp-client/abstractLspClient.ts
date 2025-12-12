import { Disposable, TextDocument, Position, Range, OutputChannel, DiagnosticSeverity, DiagnosticCollection, languages } from "vscode";
import { FeatureClient, Middleware, LanguageClientOptions, DocumentSymbol, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { SentenceManager } from "./sentenceManager";
import { WebviewManager } from "../webviewManager";
import { IFileProgressComponent } from "../components";
import { ICoqLspClient, WpDiagnostic } from "./clientTypes";
import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { OffsetDiagnostic, Severity } from "@impermeable/waterproof-editor";
import { MessageType } from "../../shared";

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}
// Seems to be needed for the mixin class below
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type ClientConstructor = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & TimeoutDisposable;

export function vscodeSeverityToWaterproof(severity: DiagnosticSeverity): Severity {
    switch (severity) {
        case DiagnosticSeverity.Error: return Severity.Error;
        case DiagnosticSeverity.Warning: return Severity.Warning;
        case DiagnosticSeverity.Information: return Severity.Information;
        case DiagnosticSeverity.Hint: return Severity.Hint;
    }
}

export function AbstractLspClient<T extends ClientConstructor>(Base: T) {
    return class extends Base implements ICoqLspClient {
        readonly disposables: Disposable[] = [];
        activeDocument: TextDocument | undefined;
        activeCursorPosition: Position | undefined;
        readonly sentenceManager: SentenceManager;
        webviewManager: WebviewManager | undefined;
        diagnosticsCollection: DiagnosticCollection;
        constructor(...args: any[]) {
            super(...args);
            this.sentenceManager = new SentenceManager();

            // send diagnostics to editor (for squiggly lines)
            this.middleware.handleDiagnostics = (uri, diagnostics_) => {

                const diagnostics = (diagnostics_ as WpDiagnostic[]);
                this.diagnosticsCollection.set(uri, diagnostics.map(d => {
                    const start = d.data?.sentenceRange?.start ?? d.range.start;
                    const end = d.data?.sentenceRange?.end ?? d.range.end;
                    return {
                        message: d.message,
                        severity: d.severity,
                        range: new Range(start, end),
                    };
                }));
            };
            
            this.disposables.push(languages.onDidChangeDiagnostics(e => {
                if (this.activeDocument === undefined) return;
                // Comparing the uris (by doing uris.includes(this.activeDocument.uri)) does not seem to achieve
                // the same result.
                if (e.uris.map(uri => uri.path).includes(this.activeDocument.uri.path)) {
                    this.processDiagnostics();
                }
            }));
        }

        getBeginningOfCurrentSentence(): Position | undefined {
            if (!this.activeDocument || !this.activeCursorPosition) return undefined;
            return this.sentenceManager.getBeginningOfSentence(this.activeCursorPosition);
        }

        getEndOfCurrentSentence(): Position | undefined {
            if (!this.activeDocument || !this.activeCursorPosition) return undefined;
            return this.sentenceManager.getEndOfSentence(this.activeCursorPosition);
        }

        // Common implementation for startWithHandlers - can be overridden
        async startWithHandlers(webviewManager: WebviewManager): Promise<void> {
            this.webviewManager = webviewManager;
            return (this as any).start();
        }

        // Common implementation for requestSymbols - can be overridden
        async requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]> {
            // Default implementation that throws - should be overridden by subclasses
            throw new Error("requestSymbols must be implemented by subclass");
        }

        // Common implementation for updateCompletions - can be overridden
        async updateCompletions(document: TextDocument): Promise<void> {
            // Default implementation that throws - should be overridden by subclasses
            throw new Error("updateCompletions must be implemented by subclass");
        }

        // Methods that subclasses must override (throw error if not implemented)
        requestGoals(params?: GoalRequest | Position): Promise<GoalAnswer<PpString>> {
            throw new Error("requestGoals must be implemented by subclass");
        }

        /**
         * Returns the notification method name for viewport hints.
         * Subclasses must override this to provide the correct notification name.
         */
        abstract getViewportNotificationName(): string;

        async sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
            if (!(this as any).isRunning()) return;

            const startPos = document.positionAt(start);
            let endPos = document.positionAt(end);

            // Compute end of document position, use that if we're close
            const endOfDocument = document.positionAt(document.getText().length);
            if (endOfDocument.line - endPos.line < 20) {
                endPos = endOfDocument;
            }

            const requestBody = {
                textDocument: VersionedTextDocumentIdentifier.create(
                    document.uri.toString(),
                    document.version
                ),
                range: {
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

            await (this as any).sendNotification(this.getViewportNotificationName(), requestBody);
        }

        createGoalsRequestParameters(document: TextDocument, position: Position): GoalRequest {
            throw new Error("createGoalsRequestParameters must be implemented by subclass");
        }

        async processDiagnostics() {
            const document = this.activeDocument;
            if (!document) return;

            const diagnostics = languages.getDiagnostics(document.uri);

            const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map(d => {
                return {
                    message: d.message,
                    severity: vscodeSeverityToWaterproof(d.severity),
                    startOffset: document.offsetAt(d.range.start),
                    endOffset: document.offsetAt(d.range.end)
                };
            });
            this.webviewManager!.postAndCacheMessage(document, {
                type: MessageType.diagnostics,
                body: { positionedDiagnostics, version: document.version }
            });
        }
    };
}
