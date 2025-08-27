import { workspace } from "vscode";
import { HypVisibility } from "../../lib/types";
import { WaterproofLogger as wpl } from "./logger";

export class WaterproofConfigHelper {

    /** Returns the Waterproof configuration object */
    static get configuration() {
        return config();
    }

    /** `waterproof.teacherMode` */
    static get teacherMode() {
        return config().get<boolean>("teacherMode") as boolean;
    }

    /** `waterproof.detailedErrorsMode` */
    static get detailedErrors() {
        return config().get<boolean>("detailedErrorsMode") as boolean;
    }

    /** `waterproof.showLineNumbersInEditor` */
    static get showLineNumbersInEditor() {
        return config().get<boolean>("showLineNumbersInEditor") as boolean;
    }

    /** `waterproof.skipLaunchChecks` */
    static get skipLaunchChecks() {
        return config().get<boolean>("skipLaunchChecks") as boolean;
    }

    /** `waterproof.showMenuItemsInEditor` */
    static get showMenuItems() {
        return config().get<boolean>("showMenuItemsInEditor") as boolean;
    }

    /** `waterproof.showLineNumbersInEditor` */
    static set showLineNumbersInEditor(value: boolean) {
        // Update the Waterproof showLineNumbersInEditor configuration
        // entry, true means we set the global configuration value.
        config().update("showLineNumbersInEditor", value, true);
    }


    /** `waterproof.enforceCorrectNonInputArea` */
    static get enforceCorrectNonInputArea() {
        return config().get<boolean>("enforceCorrectNonInputArea") as boolean;
    }

    /** `waterproof.eager_diagnostics` */
    static get eager_diagnostics() {
        return config().get<boolean>("eager_diagnostics") as boolean;
    }

    /** `waterproof.show_waterproof_info_messages` */
    static get show_waterproof_info_messages() {
        return config().get<boolean>("show_waterproof_info_messages") as boolean;
    }

    /** `waterproof.show_notices_as_diagnostics` */
    static get show_notices_as_diagnostics() {
        return config().get<boolean>("show_notices_as_diagnostics") as boolean;
    }

    /** `waterproof.max_errors` */
    static get max_errors() {
        return config().get<number>("max_errors") as number;
    }

    /** `waterproof.send_diags_extra_data */
    static get send_diags_extra_data() {
        return config().get<boolean>("send_diags_extra_data") as boolean;
    }

    /** `waterproof.ContinuousChecking` */
    static get ContinuousChecking() {
        return config().get<boolean>("ContinuousChecking") as boolean;
    }


    /** `waterproof.goal_after_tactic` */
    static get goal_after_tactic() {
        return config().get<boolean>("goal_after_tactic") as boolean;
    }

    /** `waterproof.pp_type` */
    static get pp_type() {
        return config().get<number>("pp_type") as number;
    }


    /** `waterproof.visibilityOfHypotheses` */
    static get visibilityOfHypotheses() : HypVisibility {
        const hypVisibility = config().get<string>("visibilityOfHypotheses");
        wpl.log(`Hypothesis visibility set to: ${hypVisibility}`); 
        switch(hypVisibility) {
            case "all":
                return HypVisibility.All;
            case "limited":
                return HypVisibility.Limited;
            case "none":
            default:
                return HypVisibility.None;
        }
    }
    /** `waterproof.trace.server` */
    static get trace_server() {
        return config().get<"off" | "messages" | "verbose">("trace.server") as "off" | "messages" | "verbose";
    }

    /** `waterproof.debug` */
    static get debug() {
        return config().get<boolean>("debug") as boolean;
    }

    /** `waterproof.path` */
    static get path() {
        return config().get<string>("path") as string;
    }

    /** `waterproof.args` */
    static get args() {
        return config().get<string[]>("args") as string[];
    }

    /** `waterproof.admit_on_bad_qed` */
    static get admit_on_bad_qed() {
        return config().get<boolean>("admit_on_bad_qed") as boolean;
    }

    /** `waterproof.unicode_completion` */
    static get unicode_completion() {
        return config().get<"off" | "normal" | "extended">("unicode_completion") as "off" | "normal" | "extended";
    }

    /** `waterproof.updateIgnores` */
    static get updateIgnores() {
        return config().get<boolean>("updateIgnores") as boolean;
    }


}

function config() {
    return workspace.getConfiguration("waterproof");
}
