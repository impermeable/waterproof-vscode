import { ConfigurationTarget, workspace } from "vscode";
import { HypVisibility } from "../../lib/types";

// READ THIS WHEN ADDING A NEW SETTING OR MODIFYING AN EXISTING ONE.
// Adding a setting is done by modifying the WaterproofSetting enum underneath with the new setting name.
// WaterproofSettingMap will then complain that it is incomplete, you should add the setting name there.
// and then update WaterproofSettingTypes with the proper type of the setting.
// Finally, you can use WaterproofConfigHelper.get and WaterproofConfigHelper.update to get and set the setting.

/**
 * Available settings in the `waterproof` configuration section.
 */
export enum WaterproofSetting {
    TeacherMode,
    DetailedErrorsMode,
    ShowLineNumbersInEditor,
    SkipLaunchChecks,
    ShowMenuItemsInEditor,
    EnforceCorrectNonInputArea,
    EagerDiagnostics,
    ShowWaterproofInfoMessages,
    ShowNoticesAsDiagnostics,
    MaxErrors,
    SendDiagsExtraData,
    GoalAfterTactic,
    PpType,
    VisibilityOfHypotheses,
    TraceServer,
    Debug,
    Path,
    Args,
    AdmitOnBadQed,
    UnicodeCompletion,
    UpdateIgnores
}

/**
 * Maps WaterproofSetting enum values to their string representation in the configuration.
 */
export const WaterproofSettingMap: Record<WaterproofSetting, string> = {
    [WaterproofSetting.TeacherMode]: "teacherMode",
    [WaterproofSetting.DetailedErrorsMode]: "detailedErrorsMode",
    [WaterproofSetting.ShowLineNumbersInEditor]: "showLineNumbersInEditor",
    [WaterproofSetting.SkipLaunchChecks]: "skipLaunchChecks",
    [WaterproofSetting.ShowMenuItemsInEditor]: "showMenuItemsInEditor",
    [WaterproofSetting.EnforceCorrectNonInputArea]: "enforceCorrectNonInputArea",
    [WaterproofSetting.EagerDiagnostics]: "eager_diagnostics",
    [WaterproofSetting.ShowWaterproofInfoMessages]: "show_waterproof_info_messages",
    [WaterproofSetting.ShowNoticesAsDiagnostics]: "show_notices_as_diagnostics",
    [WaterproofSetting.MaxErrors]: "max_errors",
    [WaterproofSetting.SendDiagsExtraData]: "send_diags_extra_data",
    [WaterproofSetting.GoalAfterTactic]: "goal_after_tactic",
    [WaterproofSetting.PpType]: "pp_type",
    [WaterproofSetting.VisibilityOfHypotheses]: "visibilityOfHypotheses",
    [WaterproofSetting.TraceServer]: "trace.server",
    [WaterproofSetting.Debug]: "debug",
    [WaterproofSetting.Path]: "path",
    [WaterproofSetting.Args]: "args",
    [WaterproofSetting.AdmitOnBadQed]: "admit_on_bad_qed",
    [WaterproofSetting.UnicodeCompletion]: "unicode_completion",
    [WaterproofSetting.UpdateIgnores]: "updateIgnores"
};

/**
 * Maps WaterproofSetting enum values to their types.
 */
type WaterproofSettingTypes = {
    [WaterproofSetting.TeacherMode]: boolean;
    [WaterproofSetting.DetailedErrorsMode]: boolean;
    [WaterproofSetting.ShowLineNumbersInEditor]: boolean;
    [WaterproofSetting.SkipLaunchChecks]: boolean;
    [WaterproofSetting.ShowMenuItemsInEditor]: boolean;
    [WaterproofSetting.EnforceCorrectNonInputArea]: boolean;
    [WaterproofSetting.EagerDiagnostics]: boolean;
    [WaterproofSetting.ShowWaterproofInfoMessages]: boolean;
    [WaterproofSetting.ShowNoticesAsDiagnostics]: boolean;
    [WaterproofSetting.MaxErrors]: number;
    [WaterproofSetting.SendDiagsExtraData]: boolean;
    [WaterproofSetting.GoalAfterTactic]: boolean;
    [WaterproofSetting.PpType]: number;
    [WaterproofSetting.VisibilityOfHypotheses]: HypVisibility;
    [WaterproofSetting.TraceServer]: "off" | "messages" | "verbose";
    [WaterproofSetting.Debug]: boolean;
    [WaterproofSetting.Path]: string;
    [WaterproofSetting.Args]: string[];
    [WaterproofSetting.AdmitOnBadQed]: boolean;
    [WaterproofSetting.UnicodeCompletion]: "off" | "normal" | "extended";
    [WaterproofSetting.UpdateIgnores]: boolean;
};

/**
 * Returns the fully qualified setting name for a given WaterproofSetting enum value.
 * @param setting A setting from the WaterproofSetting enum
 * @returns The fully qualified setting name, e.g., `waterproof.teacherMode`
 */
export function qualifiedSettingName(setting: WaterproofSetting): string {
    return `waterproof.${WaterproofSettingMap[setting]}`;
}

export class WaterproofConfigHelper {

    /** Returns the Waterproof configuration object */
    static get configuration() {
        return config();
    }

    /**
     * Get the configuration with name `waterproof.[setting]`
     * @param setting The configuration to retrieve.
     * @returns The configuration.
     */
    static get<T extends WaterproofSetting>(setting: T): WaterproofSettingTypes[T]
    {
        return config().get<WaterproofSettingTypes[T]>(WaterproofSettingMap[setting]) as WaterproofSettingTypes[T];
    }

    /**
     * Update the configuration with name `waterproof.[setting]`
     * @param setting The configuration to update.
     * @param value The new value.
     * @param global Whether to update the global or workspace setting.
     */
    static async update<T extends WaterproofSetting>(setting: T, value: WaterproofSettingTypes[T], target: ConfigurationTarget = ConfigurationTarget.Global) {
        return config().update(WaterproofSettingMap[setting], value, target);
    }
}

function config() {
    return workspace.getConfiguration("waterproof");
}
