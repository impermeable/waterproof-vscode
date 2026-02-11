import {
    Uri,
    Range,
    DiagnosticRelatedInformation,
    DiagnosticSeverity,
    DiagnosticTag,
    ExtensionContext,
    WorkspaceConfiguration,
    Disposable,
    Position,
    TextDocument
} from "vscode";
import { DocumentSymbol } from "vscode-languageserver-types";

import { LanguageClient as NodeLanguageClient } from "vscode-languageclient/node";
import { LanguageClient as BrowserLanguageClient } from "vscode-languageclient/browser";
import { LanguageClientOptions } from "vscode-languageclient";
import { WebviewManager } from "../webviewManager";

export interface TimeoutDisposable extends Disposable {
    dispose(timeout?: number): Promise<void>;
}

// alternatively, this could be defined as `FeatureClient<Middleware, LanguageClientOptions>`
export type LanguageClient = NodeLanguageClient | BrowserLanguageClient

export type LanguageClientProvider = () => LanguageClient;

export type LanguageClientProviderFactory = (
    context: ExtensionContext,
    clientOptions: LanguageClientOptions,
    wsConfig: WorkspaceConfiguration
) => LanguageClientProvider;
 
export interface ILspClient extends TimeoutDisposable {
    /**
     * Check whether this client is running.
     */
    isRunning(): boolean;

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
     * Registers handlers (for, e.g., file progress notifications, which
     * need to be forwarded to the * editor) and starts client.
     * Returns the language(s) of the client(s) that were started.
     */
    startWithHandlers(webviewManager: WebviewManager): Promise<string[]>;

    /**
     * Sends an LSP request to retrieve the symbols in the `activeDocument`.
     */
    requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]>;

    /**
     * Requests symbols and sends corresponding completions to the editor.
     */
    updateCompletions(document: TextDocument): Promise<void>;
}

/**
 * The following are types related to the configuration of the
 * language client
 */

/**
 * Type that represents configuration parameter allowing the user to
 * specify on which types the goals are updated
 */
export enum ShowGoalsOnCursorChange {
    Never = 0,
    OnMouse = 1,
    OnMouseAndKeyboard = 2,
    OnMouseKeyboardCommand = 3,
}

/**
 * The lsp client configuration
 */
export interface LspClientConfig {
    show_goals_on: ShowGoalsOnCursorChange;
}

// TODO: Rewrite namespace to modern syntax
// eslint-disable-next-line @typescript-eslint/no-namespace
export namespace LspClientConfig {
    export function create(): LspClientConfig {
        const obj: LspClientConfig = { show_goals_on: ShowGoalsOnCursorChange.Never };
        return obj;
    }
}

/**
 * We override the Diagnostic type from vscode to include the coq-lsp specific data
 *
 * Original: https://github.com/youngjuning/vscode-api.js.org/blob/e9ac06e/vscode.d.ts#L6781
 *
 * Additional field: `data` (https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md#extra-diagnostics-data)
 */
export interface WpDiagnostic {
    range: Range;
    message: string;
    severity: DiagnosticSeverity;
    source?: string;
    code?: string | number | {
        value: string | number;
        target: Uri;
    };
    relatedInformation?: DiagnosticRelatedInformation[];
    tags?: DiagnosticTag[];

    // Coq-LSP specific (see https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md#extra-diagnostics-data)
    data?: DiagnosticsData;
}

// See https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md#extra-diagnostics-data
// From `prefix` Require `refs`
// type failedRequire = {
//     prefix ?: qualid
//     refs : qualid list
// }

type DiagnosticsData = {
    sentenceRange?: Range;
    // failedRequire ?: FailedRequire // TODO: Unsupported by us for now
}
