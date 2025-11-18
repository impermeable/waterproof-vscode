import { Disposable, TextDocument, Position, Range, OutputChannel } from "vscode";
import { FeatureClient, Middleware, LanguageClientOptions, DocumentSymbol,  } from "vscode-languageclient";
import { SentenceManager } from "./sentenceManager";
import { WebviewManager } from "../webviewManager";
import { IFileProgressComponent } from "../components";
import { ICoqLspClient } from "./clientTypes";
import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}
// Seems to be needed for the mixin class below
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type ClientConstructor = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & TimeoutDisposable;

export function AbstractLspClient<T extends ClientConstructor>(Base: T) {
    return class extends Base implements ICoqLspClient {
        readonly disposables: Disposable[] = [];
        activeDocument: TextDocument | undefined;
        activeCursorPosition: Position | undefined;
        readonly sentenceManager: SentenceManager;
        webviewManager: WebviewManager | undefined;

        constructor(...args: any[]) {
            super(...args);
            this.sentenceManager = new SentenceManager();
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

        sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
            throw new Error("sendViewportHint must be implemented by subclass");
        }

        createGoalsRequestParameters(document: TextDocument, position: Position): GoalRequest {
            throw new Error("createGoalsRequestParameters must be implemented by subclass");
        }
    };
}
