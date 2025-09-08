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

    /** `waterproof.eagerDiagnostics` */
    static get eagerDiagnostics() {
        return config().get<boolean>("eagerDiagnostics") as boolean;
    }

    /** `waterproof.showWaterproofInfoMessages` */
    static get showWaterproofInfoMessages() {
        return config().get<boolean>("showWaterproofInfoMessages") as boolean;
    }

    /** `waterproof.showNoticesAsDiagnostics` */
    static get showNoticesAsDiagnostics() {
        return config().get<boolean>("showNoticesAsDiagnostics") as boolean;
    }

    /** `waterproof.maxErrors` */
    static get maxErrors() {
        return config().get<number>("maxErrors") as number;
    }

    /** `waterproof.sendDiagsExtraData` */
    static get sendDiagsExtraData() {
        return config().get<boolean>("sendDiagsExtraData") as boolean;
    }

    /** `waterproof.ContinuousChecking` */
    static get ContinuousChecking() {
        return config().get<boolean>("ContinuousChecking") as boolean;
    }


    /** `waterproof.goalAfterTactic` */
    static get goalAfterTactic() {
        return config().get<boolean>("goalAfterTactic") as boolean;
    }

    /** `waterproof.ppType` */
    static get ppType() {
        return config().get<number>("ppType") as 0 | 1 | 2;
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

    /** `waterproof.admitOnBadQed` */
    static get admitOnBadQed() {
        return config().get<boolean>("admitOnBadQed") as boolean;
    }

    /** `waterproof.unicodeCompletion` */
    static get unicodeCompletion() {
        return config().get<"off" | "normal" | "extended">("unicodeCompletion") as "off" | "normal" | "extended";
    }

    /** `waterproof.updateIgnores` */
    static get updateIgnores() {
        return config().get<boolean>("updateIgnores") as boolean;
    }


}

function config() {
    return workspace.getConfiguration("waterproof");
}
