import { extensions, window, workspace } from "vscode";

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
    let activationConfig = workspace.getConfiguration();
    let updateIgnores = activationConfig.get("waterproof.updateIgnores") ?? true;
    if (updateIgnores) {
        let fexc: any = activationConfig.get("files.exclude");
        activationConfig.update("files.exclude", {
            "**/*.vo": true,
            "**/*.vok": true,
            "**/*.vos": true,
            "**/*.aux": true,
            "**/*.glob": true,
            ...fexc,
        });
    }
}
