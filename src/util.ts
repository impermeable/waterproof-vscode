import { env, extensions, ExtensionContext, Uri, window, commands, workspace } from "vscode";
import { WaterproofConfigHelper, WaterproofLogger as wpl, WaterproofSetting } from "./helpers";

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

const CONFLICTING_EXTENSIONS: { id: string; label: string }[] = [
    { id: "leanprover.lean4", label: "Lean 4" },
    { id: "ejgallego.coq-lsp", label: "Coq LSP" },
    { id: "maximedenes.vscoq", label: "VSCoq" },
    { id: "rocq-prover.vsrocq", label: "VSRocq" }
];

/**
 * Checks whether any conflicting extensions are installed and, if so, offers to set up a
 * dedicated VS Code profile where they are all disabled.
 */
export async function checkConflictingExtensions(context: ExtensionContext): Promise<void> {
    const conflicting = CONFLICTING_EXTENSIONS.filter(e => extensions.getExtension(e.id));
    if (!conflicting.length) return;

    const names = conflicting.map(e => e.label).join(", ");
    const selection = await window.showWarningMessage(
        `The following extensions conflict with Waterproof: ${names}. Set up a dedicated 'Waterproof' profile that only includes the Waterproof extensions?`,
        "Set up Waterproof Profile",
        "Dismiss",
    );
    if (selection === "Set up Waterproof Profile") {
        await setupWaterproofProfile(context);
    }
}

async function setupWaterproofProfile(context: ExtensionContext): Promise<void> {
    try {
        const WATERPROOF_EXTENSIONS = ["waterproof-tue.waterproof", "waterproof-tue.waterproof-river"];
        const profileExtensions = WATERPROOF_EXTENSIONS
            .filter(id => extensions.getExtension(id))
            .map(id => ({ identifier: { id } }));

        const profile = {
            name: "Waterproof",
            useDefaultFlags: { settings: true, keybindings: true, tasks: true, snippets: true },
            extensions: JSON.stringify(profileExtensions),
        };

        const profileUri = Uri.joinPath(context.globalStorageUri, "waterproof.code-profile");
        await workspace.fs.writeFile(profileUri, new TextEncoder().encode(JSON.stringify(profile, null, 2)));
        wpl.log("Wrote Waterproof profile to " + profileUri.fsPath);

        await commands.executeCommand("workbench.profiles.actions.manageProfiles");

        const selection = await window.showInformationMessage(
            `Profile ready. In the Profile Manager, click 'Import Profile...' and select: ${profileUri.fsPath}`,
            "Copy Path"
        );
        if (selection === "Copy Path") {
            await env.clipboard.writeText(profileUri.fsPath);
        }
    } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        wpl.log("Failed to write Waterproof profile: " + message);
        window.showErrorMessage(
            "Something went wrong while preparing the Waterproof profile. Please report this as a bug.",
        );
    }
}

/**
 * Checks whether the user wants to ignore Rocq object files and adjusts the workspace
 * configuration accordingly.
 */
export function excludeRocqFileTypes() {
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