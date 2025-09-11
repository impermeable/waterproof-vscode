import { extensions, window, workspace } from "vscode";
import { WaterproofConfigHelper, WaterproofSetting } from "./helpers";

/**
 * Returns a random alphanumerical string of length 32.
 */
export function getNonce() {
    let text = '';
    const possible = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    for (let i = 0; i < 32; i++) {
        text += possible.charAt(Math.floor(Math.random() * possible.length));
    }
    return text;
}

/**
 * Checks whether any conflicting extensions are enabled, and warns the user in that case.
 */
export function checkConflictingExtensions() {
    const conflicting: string[] = [];

    // note: `isActive` can be false, even if extension activates later
    // this way of checking correctly ignores disabled extensions
    if (extensions.getExtension("ejgallego.coq-lsp")) conflicting.push("Coq LSP");
    if (extensions.getExtension("maximedenes.vscoq")) conflicting.push("VSCoq");

    // show warning if any conflicting extensions are present
    if (conflicting.length) {
        window.showErrorMessage(
            "The following extensions must be disabled for Waterproof to work properly: " + conflicting.join(", "),
            "Dismiss"  // although it does nothing, this action item causes the message to be expanded
        );
    }
}

/**
 * Checks whether the user wants to ignore Coq object files and adjusts the workspace
 * configuration accordingly.
 */
export function excludeCoqFileTypes() {
    const updateIgnores = WaterproofConfigHelper.get(WaterproofSetting.UpdateIgnores);
    if (updateIgnores) {
        const config = workspace.getConfiguration();
        const fexc = config.get<object>("files.exclude") as object;
        config.update("files.exclude", {
            "**/*.vo": true,
            "**/*.vok": true,
            "**/*.vos": true,
            "**/*.aux": true,
            "**/*.glob": true,
            ...fexc,
        });
    }
}
