import { env, extensions, Uri, window, commands, workspace } from "vscode";
import { WaterproofConfigHelper, WaterproofLogger as wpl, WaterproofSetting } from "./helpers";
import { writeFileSync } from "fs";
import { tmpdir } from "os";
import { join } from "path";

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
 * Lean 4 conflicts are handled separately by {@link checkLeanConflict}.
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
 * Checks whether the Lean 4 extension is installed and, if so, offers to set up a dedicated
 * VS Code profile where Lean 4 is disabled.
 */
export function checkLeanConflict() {
    if (!extensions.getExtension("leanprover.lean4")) return;

    window.showWarningMessage(
        "The Lean 4 extension conflicts with Waterproof. Set up a 'Waterproof' profile for easy switching?",
        "Set up Waterproof Profile",
        "Dismiss",
    ).then((selection) => {
        if (selection === "Set up Waterproof Profile") {
            setupWaterproofProfile();
        }
    });
}

async function setupWaterproofProfile(): Promise<void> {
    try {
        const profileExtensions = [
            ...extensions.all
                .filter(ext => !ext.packageJSON.isBuiltin && ext.id !== "leanprover.lean4")
                .map(ext => ({ identifier: { id: ext.id }, version: ext.packageJSON.version })),
            // Explicitly disable Lean 4, even if it is application-scoped
            { identifier: { id: "leanprover.lean4" }, disabled: true },
        ];

        const profile = {
            name: "Waterproof",
            useDefaultFlags: { settings: true, keybindings: true, tasks: true, snippets: true },
            extensions: JSON.stringify(profileExtensions),
        };

        const profilePath = join(tmpdir(), "waterproof.code-profile");
        writeFileSync(profilePath, JSON.stringify(profile, null, 2), "utf8");
        wpl.log("Wrote Waterproof profile to " + profilePath);

        await commands.executeCommand("workbench.profiles.actions.manageProfiles");

        const selection = await window.showInformationMessage(
            `Profile ready. In the Profile Manager, click 'Import Profile...' and select: ${profilePath}`,
            "Copy Path"
        );
        if (selection === "Copy Path") {
            await env.clipboard.writeText(profilePath);
        }
    } catch (err) {
        wpl.log("Failed to write Waterproof profile: " + err);
        window.showErrorMessage(
            "Something went wrong while preparing the Waterproof profile. Please report this as a bug.",
            "Report Bug"
        ).then((selection) => {
            if (selection === "Report Bug") {
                env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-vscode/issues"));
            }
        });
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

/**
 * Checks whether the user has enabled the setting `trimTrailingWhitespace`, and warns the
 * user in that case.
 */
export function checkTrimmingWhitespace() {
    const config = workspace.getConfiguration('files');
    const isTrimTrailingWhitespaceEnabled = config.get<boolean>('trimTrailingWhitespace');
    if (isTrimTrailingWhitespaceEnabled) {
        window.showWarningMessage(
            "The setting `Trim Trailing Whitespace` is enabled. This may cause unexpected behaviour in Waterproof, and we thus recommend you to turn it off.",
            "Open Settings",
            "Dismiss"
        ).then((selection) => {
            if (selection === "Open Settings") {
                commands.executeCommand('workbench.action.openSettings', 'Trim Trailing Whitespace');
            }
        });
    }
}