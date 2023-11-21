import { WorkspaceConfiguration, workspace } from "vscode";

export class WaterproofConfigHelper {
    /** `waterproof.teacherMode` */
    static get teacherMode() {
        return wpConfig().get<boolean>("teacherMode") as boolean;
    }

    /** `waterproof.enforceCorrectNonInputArea` */
    static get enforceCorrectNonInputArea() {
        return wpConfig().get<boolean>("teacherMode") as boolean;
    }

    /** `waterproof.standardCoqSyntax` */
    static get standardCoqSyntax() {
        return wpConfig().get<boolean>("standardCoqSyntax") as boolean;
    }

    /** `waterproof.eager_diagnostics` */
    static get eager_diagnostics() {
        return wpConfig().get<boolean>("eager_diagnostics") as boolean;
    }

    /** `waterproof.args` */
    static get args() {
        return wpConfig().get<Array<string>>("args") as Array<string>;
    }

    /** `waterproof.path` */
    static get path() {
        return wpConfig().get<string>("path") as string;
    }
}

/** Return the `Waterproof` WorkspaceConfiguration object */
export const wpConfig = (): WorkspaceConfiguration => {
    return workspace.getConfiguration("waterproof");
}