import { WaterproofConfigHelper, WaterproofSetting } from "../../helpers";

/**
 * The Coq LSP server configuration
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
