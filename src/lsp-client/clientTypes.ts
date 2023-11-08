import { Position, TextDocument, WorkspaceConfiguration } from "vscode";
import { BaseLanguageClient, DocumentSymbol, LanguageClientOptions } from "vscode-languageclient";

import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { WebviewManager } from "../webviewManager";
import { SentenceManager } from "./sentenceManager";

/**
 * The following are types related to the language client and the
 * extended interface it provides
 */

/**
 * Interface for the added methods of the language client
 */
export interface ICoqLspClient {
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

    /**
     * Registers handlers (for, e.g., file progress notifications, which need to be forwarded to the
     * editor) and starts client.
     */
    startWithHandlers(webviewManager: WebviewManager): Promise<void>;

    /**
     * Returns the end position of the currently selected sentence, i.e., the Coq sentence in the
     * active document in which the text cursor is located. Only returns `undefined` if no sentences
     * are known.
     */
    getEndOfCurrentSentence(): Position | undefined;

    /**
     * Returns the beginning position of the currently selected sentence, i.e., the Coq sentence in the
     * active document in which the text cursor is located. Only returns `undefined` if no sentences
     * are known. This is really just the end position of the previous sentence.
     */
    getBeginningOfCurrentSentence(): Position | undefined

    /**
     * Creates parameter object for a goals request.
     */
    createGoalsRequestParameters(document: TextDocument, position: Position): GoalRequest;

    /** Sends an LSP request with the specified parameters to retrieve the goals. */
    requestGoals(parameters: GoalRequest): Promise<GoalAnswer<PpString>>;
    /** Sends an LSP request to retrieve the goals at `position` in the active document. */
    requestGoals(position: Position): Promise<GoalAnswer<PpString>>;
    /** Sends an LSP request to retrieve the goals at the active cursor position. */
    requestGoals(): Promise<GoalAnswer<PpString>>;

    /** Sends an LSP request to retrieve the symbols in the specified `document`. */
    requestSymbols(document: TextDocument): Promise<DocumentSymbol[]>;
    /** Sends an LSP request to retrieve the symbols in the `activeDocument`. */
    requestSymbols(): Promise<DocumentSymbol[]>;

    /**
     * Requests symbols and sends corresponding completions to the editor.
     */
    updateCompletions(document: TextDocument): Promise<void>;
}

/**
 * Type of file language client
 */
export type CoqLspClient = BaseLanguageClient & ICoqLspClient;

/**
 * Type of file language client factory
 */
export type CoqLspClientFactory = (
    clientOptions: LanguageClientOptions,
    wsConfig: WorkspaceConfiguration
) => CoqLspClient;



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
export interface CoqLspClientConfig {
    show_goals_on: ShowGoalsOnCursorChange;
}

/**
 * The lsp server configuration
 */
export interface CoqLspServerConfig {
    client_version: string;
    eager_diagnostics: boolean;
    goal_after_tactic: boolean;
    show_coq_info_messages: boolean;
    show_notices_as_diagnostics: boolean;
    admit_on_bad_qed: boolean;
    debug: boolean;
    unicode_completion: "off" | "normal" | "extended";
    max_errors: number;
    pp_type: 0 | 1 | 2;
    show_stats_on_hover: boolean;
}


export namespace CoqLspServerConfig {
    export function create(
        client_version: string,
        wsConfig: any
    ): CoqLspServerConfig {
        return {
            client_version: client_version,
            eager_diagnostics: wsConfig.eager_diagnostics,
            goal_after_tactic: wsConfig.goal_after_tactic,
            show_coq_info_messages: wsConfig.show_coq_info_messages,
            show_notices_as_diagnostics: wsConfig.show_notices_as_diagnostics,
            admit_on_bad_qed: wsConfig.admit_on_bad_qed,
            debug: wsConfig.debug,
            unicode_completion: wsConfig.unicode_completion,
            max_errors: wsConfig.max_errors,
            pp_type: wsConfig.pp_type,
            show_stats_on_hover: wsConfig.show_stats_on_hover,
        };
    }
}

export namespace CoqLspClientConfig {
    export function create(wsConfig: any): CoqLspClientConfig {
        let obj: CoqLspClientConfig = { show_goals_on: wsConfig.show_goals_on };
        return obj;
    }
}
