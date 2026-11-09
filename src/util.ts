import {
  ConfigurationScope,
  env,
  extensions,
  ExtensionContext,
  Uri,
  window,
  commands,
  workspace,
} from "vscode";
import {
  WaterproofConfigHelper,
  WaterproofLogger as wpl,
  WaterproofSetting,
} from "./helpers";

/**
 * Returns a random alphanumerical string of length 32.
 */
export function getNonce() {
  let text = "";
  const possible =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
  for (let i = 0; i < 32; i++) {
    text += possible.charAt(Math.floor(Math.random() * possible.length));
  }
  return text;
}

const CONFLICTING_EXTENSIONS: { id: string; label: string }[] = [
  { id: "leanprover.lean4", label: "Lean 4" },
  { id: "ejgallego.coq-lsp", label: "Coq LSP" },
  { id: "maximedenes.vscoq", label: "VSCoq" },
  { id: "rocq-prover.vsrocq", label: "VSRocq" },
];

/**
 * Checks whether any conflicting extensions are installed and, if so, offers to set up a
 * dedicated VS Code profile where they are all disabled.
 */
export async function checkConflictingExtensions(
  context: ExtensionContext,
): Promise<void> {
  const conflicting = CONFLICTING_EXTENSIONS.filter((e) =>
    extensions.getExtension(e.id),
  );
  if (!conflicting.length) return;

  const names = conflicting.map((e) => e.label).join(", ");
  const selection = await window.showWarningMessage(
    `The following extensions conflict with Waterproof: ${names}. Set up a dedicated 'Waterproof' profile that only includes the Waterproof extensions?`,
    "Set up Waterproof Profile",
    "Dismiss",
  );
  if (selection === "Set up Waterproof Profile") {
    await setupWaterproofProfile(context);
  }
}

async function setupWaterproofProfile(
  context: ExtensionContext,
): Promise<void> {
  try {
    const WATERPROOF_EXTENSIONS = [
      "waterproof-tue.waterproof",
      "waterproof-tue.waterproof-river",
    ];
    const profileExtensions = WATERPROOF_EXTENSIONS.filter((id) =>
      extensions.getExtension(id),
    ).map((id) => ({ identifier: { id } }));

    const profile = {
      name: "Waterproof",
      useDefaultFlags: {
        settings: true,
        keybindings: true,
        tasks: true,
        snippets: true,
      },
      extensions: JSON.stringify(profileExtensions),
    };

    const profileUri = Uri.joinPath(
      context.globalStorageUri,
      "waterproof.code-profile",
    );
    await workspace.fs.writeFile(
      profileUri,
      new TextEncoder().encode(JSON.stringify(profile, null, 2)),
    );
    wpl.log("Wrote Waterproof profile to " + profileUri.fsPath);

    await commands.executeCommand("workbench.profiles.actions.manageProfiles");

    const selection = await window.showInformationMessage(
      `Profile ready. In the Profile Manager, click 'Import Profile...' and select: ${profileUri.fsPath}`,
      "Copy Path",
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
  const updateIgnores = WaterproofConfigHelper.get(
    WaterproofSetting.UpdateIgnores,
  );
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

/** Settings in the `files` section with which VS Code changes the text of a document on save. */
const TEXT_CHANGING_SAVE_SETTINGS = [
  "trimTrailingWhitespace",
  "trimFinalNewlines",
  "insertFinalNewline",
] as const;

/**
 * Returns the settings (without the `files.` prefix) with which VS Code would change the text of
 * a document in `scope` when saving it.
 */
export function enabledTextChangingSaveSettings(
  scope: ConfigurationScope,
): string[] {
  const config = workspace.getConfiguration("files", scope);
  return TEXT_CHANGING_SAVE_SETTINGS.filter((setting) =>
    config.get<boolean>(setting, false),
  );
}

/** The combination of settings that was last warned about, to avoid repeating the warning. */
let lastWarnedSaveSettings = "";

/**
 * Warns the user when settings that change the document text on save are enabled for `scope`.
 * The warning is shown again only when the combination of enabled settings changes.
 */
export function checkTextChangingSaveSettings(scope: ConfigurationScope) {
  const enabled = enabledTextChangingSaveSettings(scope);
  const key = enabled.join(",");
  if (key === lastWarnedSaveSettings) return;
  lastWarnedSaveSettings = key;
  if (enabled.length === 0) return;

  const names = enabled.map((setting) => `\`files.${setting}\``).join(", ");
  window
    .showWarningMessage(
      `The following settings change the document when saving: ${names}. This may cause unexpected behaviour in Waterproof, and we thus recommend you to turn them off.`,
      "Open Settings",
      "Dismiss",
    )
    .then((selection) => {
      if (selection === "Open Settings") {
        commands.executeCommand(
          "workbench.action.openSettings",
          `@id:${enabled.map((setting) => `files.${setting}`).join(",")}`,
        );
      }
    });
}
