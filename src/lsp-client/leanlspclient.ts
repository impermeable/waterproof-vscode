import { ExtensionContext, workspace } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

let leanClient: LanguageClient | undefined;

export async function activateLeanClient(context: ExtensionContext): Promise<void> {
    if (leanClient) return;

    const cfg = workspace.getConfiguration("lean");
    const exe = (cfg.get<string>("executablePath") || "").trim() || "lean";
    const command = exe;
    const args = ["--server"];

    const serverOptions: ServerOptions = { command, args };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ language: "lean", scheme: "file" }, { language: "lean", scheme: "untitled" }],
        outputChannelName: "Lean LSP",
        // revealOutputChannelOn: RevealOutputChannelOn.Info is optional; numeric 1 corresponds to Info.
        revealOutputChannelOn: 1
    };

    leanClient = new LanguageClient("lean", "Lean Language Server", serverOptions, clientOptions);
    try {
        await leanClient.start();
        console.log("Lean LSP started");
    } catch (err) {
        console.error("Failed to start Lean LSP:", err);
    }
}

export async function deactivateLeanClient(): Promise<void> {
    if (!leanClient) return;
    try {
        await leanClient.stop();
        leanClient = undefined;
        console.log("Lean LSP stopped");
    } catch (err) {
        console.error("Error stopping Lean LSP:", err);
    }
}

export async function restartLeanClient(context: ExtensionContext): Promise<void> {
    await deactivateLeanClient();
    await activateLeanClient(context);
}