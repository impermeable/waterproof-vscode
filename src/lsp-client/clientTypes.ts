import { Position, ExtensionContext, TextDocument, Uri, WorkspaceConfiguration, Range, DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag } from "vscode";
import { BaseLanguageClient, DocumentSymbol, LanguageClientOptions } from "vscode-languageclient";

import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { WebviewManager } from "../webviewManager";
import { SentenceManager } from "./sentenceManager";
import { WaterproofConfigHelper, WaterproofSetting } from "../helpers";

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

    sendViewportHint(document: TextDocument, start: number, end: number): Promise<void>;

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
    context: ExtensionContext,
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
    send_diags_extra_data: boolean;
    check_only_on_request: boolean;
    send_execinfo: boolean;
}

// TODO: Rewrite namespace to modern syntax
// eslint-disable-next-line @typescript-eslint/no-namespace
export namespace CoqLspServerConfig {
    export function create(
        client_version: string
    ): CoqLspServerConfig {
        return {
            client_version: client_version,
            eager_diagnostics: WaterproofConfigHelper.get(WaterproofSetting.EagerDiagnostics),
            goal_after_tactic: WaterproofConfigHelper.get(WaterproofSetting.GoalAfterTactic),
            show_coq_info_messages: WaterproofConfigHelper.get(WaterproofSetting.ShowWaterproofInfoMessages),
            show_notices_as_diagnostics: WaterproofConfigHelper.get(WaterproofSetting.ShowNoticesAsDiagnostics),
            admit_on_bad_qed: WaterproofConfigHelper.get(WaterproofSetting.AdmitOnBadQed),
            debug: WaterproofConfigHelper.get(WaterproofSetting.Debug),
            unicode_completion: WaterproofConfigHelper.get(WaterproofSetting.UnicodeCompletion),
            max_errors: WaterproofConfigHelper.get(WaterproofSetting.MaxErrors),
            pp_type: WaterproofConfigHelper.get(WaterproofSetting.PpType),
            send_diags_extra_data: WaterproofConfigHelper.get(WaterproofSetting.SendDiagsExtraData),
            check_only_on_request: !WaterproofConfigHelper.get(WaterproofSetting.ContinuousChecking),
            send_execinfo: WaterproofConfigHelper.get(WaterproofSetting.SendExecInfo),
        };
    }
}

// TODO: Rewrite namespace to modern syntax
// eslint-disable-next-line @typescript-eslint/no-namespace
export namespace CoqLspClientConfig {
    export function create(): CoqLspClientConfig {
        const obj: CoqLspClientConfig = { show_goals_on: ShowGoalsOnCursorChange.Never };
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
    sentenceRange ?: Range;
    // failedRequire ?: FailedRequire // TODO: Unsupported by us for now
}