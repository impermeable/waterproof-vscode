import { ExtensionContext, workspace } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { AbstractLspClient } from "./abstractLspClient";

type LC = new (...args: any[]) => any;
const Mixed = AbstractLspClient((LanguageClient as unknown) as LC);


export class LeanLspClient extends (Mixed as any) {
    private readonly context: ExtensionContext;

    constructor(context: ExtensionContext, clientOptions?: LanguageClientOptions) {
        const cfg = workspace.getConfiguration("waterproof");
        const lakePath = (cfg.get<string>("lean.lakePath") || "lake").trim() || "lake";
        const serverArgs = cfg.get<string[]>("lean.serverArgs") || ["serve"];

        const serverOptions: ServerOptions = ({ command: lakePath, args: serverArgs } as unknown) as ServerOptions;

        const defaultClientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "lean4", scheme: "file" }, { language: "lean4", scheme: "untitled" }],
            outputChannelName: "Lean LSP",
            revealOutputChannelOn: 1
        };
        super("lean", "Lean Language Server", serverOptions, clientOptions || defaultClientOptions);

        this.context = context;
    }

    // Implement required abstract methods from AbstractLspClient as minimal stubs.
    requestGoals(params?: any): Promise<any> {
        return Promise.reject(new Error("requestGoals not implemented for LeanLspClient"));
    }

    sendViewportHint(document: TextDocument, start: number, end: number): Promise<void> {
        // No viewport hint for Lean in this minimal client.
        return Promise.resolve();
    }

    createGoalsRequestParameters(document: TextDocument, position: Position): any {
        return { textDocument: { uri: document.uri.toString(), version: document.version }, position };
    }


    /// ---
let leanClientInstance: LeanLspClient | undefined;


export async function activateLeanClient(context: ExtensionContext): Promise<void> {
    if (leanClientInstance) return;

    const cfg = workspace.getConfiguration("lean");
    const exe = (cfg.get<string>("executablePath") || "").trim() || "lean";
    const command = exe;
    const args = ["--server"];

    const serverOptions: ServerOptions = { command, args };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ language: "lean", scheme: "file" }, { language: "lean", scheme: "untitled" }],
        outputChannelName: "Lean LSP",
        revealOutputChannelOn: 1
    };

    leanClientInstance = new LeanLspClient(context, clientOptions);
    try {
        await leanClientInstance.start();
        console.log("Lean LSP started");
    } catch (err) {
        console.error("Failed to start Lean LSP:", err);
    }
}

export async function deactivateLeanClient(): Promise<void> {
    if (!leanClientInstance) return;
    try {
        await leanClientInstance.stop();
        leanClientInstance = undefined;
        console.log("Lean LSP stopped");
    } catch (err) {
        console.error("Error stopping Lean LSP:", err);
    }
}

export async function restartLeanClient(context: ExtensionContext): Promise<void> {
    await deactivateLeanClient();
    await activateLeanClient(context);
}