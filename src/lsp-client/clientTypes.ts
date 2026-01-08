import { Uri, Range, DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag, ExtensionContext } from "vscode";

import { WaterproofConfigHelper, WaterproofSetting } from "../helpers";
import { LanguageClientOptions } from "vscode-languageclient";
import { LspClient } from "./abstractLspClient";

export type LspClientFactory<LspClientT extends LspClient<any, any>> =
    (context: ExtensionContext, clientOptions: LanguageClientOptions, kind: ClientKind) => LspClientT;

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
            check_only_on_request: !WaterproofConfigHelper.get(WaterproofSetting.ContinuousChecking)
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
    sentenceRange?: Range;
    // failedRequire ?: FailedRequire // TODO: Unsupported by us for now
}

export type ClientKind = 'rocq' | 'lean';
