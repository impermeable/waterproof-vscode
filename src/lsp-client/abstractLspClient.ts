import { Disposable, TextDocument, Position, Range, OutputChannel } from "vscode";
import { FeatureClient, Middleware, LanguageClientOptions } from "vscode-languageclient/node";
import { SentenceManager } from "./sentenceManager";
import { WebviewManager } from "../webviewManager";
import { IFileProgressComponent } from "../components";

interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}
// Seems to be needed for the mixin class below
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export type ClientConstructor = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & TimeoutDisposable;

export function AbstractLspClient<T extends ClientConstructor>(Base: T) {
    return class extends Base {
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

        // Methods that subclasses must override (throw error if not implemented)
        requestGoals(params?: any): Promise<any> {
            throw new Error("requestGoals must be implemented by subclass");
        }

        sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
            throw new Error("sendViewportHint must be implemented by subclass");
        }

        createGoalsRequestParameters(document: TextDocument, position: Position): any {
            throw new Error("createGoalsRequestParameters must be implemented by subclass");
        }
    };
}
