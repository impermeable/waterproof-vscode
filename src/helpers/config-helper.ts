import { workspace } from "vscode";

export namespace WaterproofConfigHelper {
    export function teacherMode() {
        return workspace.getConfiguration("waterproof").get<boolean>("teacherMode") as boolean;
    }

    export function enforceCorrectNonInputArea() {
        return workspace.getConfiguration("waterproof").get<boolean>("teacherMode") as boolean;
    }

    export function standardCoqSyntax() {
        return workspace.getConfiguration("waterproof").get<boolean>("standardCoqSyntax") as boolean;
    }
}