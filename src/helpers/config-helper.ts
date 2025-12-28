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
    AdmitOnBadQed,
    Args,
    ContinuousChecking,
    Debug,
    DetailedErrorsMode,
    EagerDiagnostics,
    EnforceCorrectNonInputArea,
    GoalAfterTactic,
    LogDebugStatements,
    MaxErrors,
    Path,
    PpType,
    SendDiagsExtraData,
    SendExecInfo,
    ShowLineNumbersInEditor,
    ShowMenuItemsInEditor,
    ShowNoticesAsDiagnostics,
    ShowWaterproofInfoMessages,
    SkipLaunchChecks,
    TeacherMode,
    TraceServer,
    UnicodeCompletion,
    UpdateIgnores,
    VisibilityOfHypotheses,
}

/**
 * Maps WaterproofSetting enum values to their string representation in the configuration.
 */
export const WaterproofSettingMap: Record<WaterproofSetting, string> = {
    [WaterproofSetting.AdmitOnBadQed]: "admitOnBadQed",
    [WaterproofSetting.Args]: "args",
    [WaterproofSetting.ContinuousChecking]: "ContinuousChecking",
    [WaterproofSetting.Debug]: "debug",
    [WaterproofSetting.DetailedErrorsMode]: "detailedErrorsMode",
    [WaterproofSetting.EagerDiagnostics]: "eagerDiagnostics",
    [WaterproofSetting.EnforceCorrectNonInputArea]: "enforceCorrectNonInputArea",
    [WaterproofSetting.GoalAfterTactic]: "goalAfterTactic",
    [WaterproofSetting.LogDebugStatements]: "LogDebugStatements",
    [WaterproofSetting.MaxErrors]: "maxErrors",
    [WaterproofSetting.Path]: "path",
    [WaterproofSetting.PpType]: "ppType",
    [WaterproofSetting.SendDiagsExtraData]: "sendDiagsExtraData",
    [WaterproofSetting.SendExecInfo]: "sendExecutionInformation",
    [WaterproofSetting.ShowLineNumbersInEditor]: "showLineNumbersInEditor",
    [WaterproofSetting.ShowMenuItemsInEditor]: "showMenuItemsInEditor",
    [WaterproofSetting.ShowNoticesAsDiagnostics]: "showNoticesAsDiagnostics",
    [WaterproofSetting.ShowWaterproofInfoMessages]: "showWaterproofInfoMessages",
    [WaterproofSetting.SkipLaunchChecks]: "skipLaunchChecks",
    [WaterproofSetting.TeacherMode]: "teacherMode",
    [WaterproofSetting.TraceServer]: "trace.server",
    [WaterproofSetting.UnicodeCompletion]: "unicodeCompletion",
    [WaterproofSetting.UpdateIgnores]: "updateIgnores",
    [WaterproofSetting.VisibilityOfHypotheses]: "visibilityOfHypotheses",
};

/**
 * Maps WaterproofSetting enum values to their types.
 */
type WaterproofSettingTypes = {
    [WaterproofSetting.AdmitOnBadQed]: boolean;
    [WaterproofSetting.Args]: string[];
    [WaterproofSetting.ContinuousChecking]: boolean;
    [WaterproofSetting.Debug]: boolean;
    [WaterproofSetting.DetailedErrorsMode]: boolean;
    [WaterproofSetting.EagerDiagnostics]: boolean;
    [WaterproofSetting.EnforceCorrectNonInputArea]: boolean;
    [WaterproofSetting.GoalAfterTactic]: boolean;
    [WaterproofSetting.LogDebugStatements]: boolean;
    [WaterproofSetting.MaxErrors]: number;
    [WaterproofSetting.Path]: string;
    [WaterproofSetting.PpType]: 0 | 1 | 2;
    [WaterproofSetting.SendDiagsExtraData]: boolean;
    [WaterproofSetting.SendExecInfo]: boolean;
    [WaterproofSetting.ShowLineNumbersInEditor]: boolean;
    [WaterproofSetting.ShowMenuItemsInEditor]: boolean;
    [WaterproofSetting.ShowNoticesAsDiagnostics]: boolean;
    [WaterproofSetting.ShowWaterproofInfoMessages]: boolean;
    [WaterproofSetting.SkipLaunchChecks]: boolean;
    [WaterproofSetting.TeacherMode]: boolean;
    [WaterproofSetting.TraceServer]: "off" | "messages" | "verbose";
    [WaterproofSetting.UnicodeCompletion]: "off" | "normal" | "extended";
    [WaterproofSetting.UpdateIgnores]: boolean;
    [WaterproofSetting.VisibilityOfHypotheses]: HypVisibility;
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
