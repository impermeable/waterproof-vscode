import { ExtensionContext, workspace, window, TextDocument, Position, OutputChannel, commands } from "vscode";
import { Trace } from "vscode-languageclient/node";
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

        const leanExe =
            workspace.getConfiguration("lean").get<string>("executablePath")?.trim() || "lean";

        const serverOptions: ServerOptions = {
            command: leanExe,
            args: ["--server"],
            options: { env: process.env }
        };

        const lspTraceChannel = window.createOutputChannel("Lean LSP (Trace)");
        lspTraceChannel.show(true);

        const defaultClientOptions: LanguageClientOptions = {
            documentSelector: [
                { language: "lean4", scheme: "file" },
                { language: "lean4", scheme: "untitled" }
            ],
            outputChannelName: "Lean LSP",
            traceOutputChannel: lspTraceChannel,
            revealOutputChannelOn: 1
        };
        super("lean", "Lean Language Server", serverOptions, clientOptions ?? defaultClientOptions);
        (this as any).trace = Trace.Verbose;
        (this as any).setTrace?.(Trace.Verbose);
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
}
/// ---
let leanClientInstance: LeanLspClient | undefined;
// lightweight debug output channel 
const leanDebugOutput: OutputChannel = window.createOutputChannel("Lean LSP Debug");

export function getLeanInstance(): LeanLspClient | undefined {
    return leanClientInstance;
}

export async function activateLeanClient(context: ExtensionContext): Promise<void> {
    if (leanClientInstance) return;

    leanDebugOutput.show(true);
    leanDebugOutput.appendLine("[LeanLspClient] activateLeanClient()");

    try {
        leanClientInstance = new LeanLspClient(context, undefined);
        context.subscriptions.push(leanDebugOutput);
        (leanClientInstance as any).trace = Trace.Verbose;
        (leanClientInstance as any).setTrace?.(Trace.Verbose);


        leanDebugOutput.appendLine("[LeanLspClient] calling start()");
        await leanClientInstance.start();
        leanDebugOutput.appendLine("[LeanLspClient] start() resolved");

        (leanClientInstance as any).onDidChangeState?.(({ newState }: any) => {
            const name = newState === 2 ? "Running" : newState === 1 ? "Starting" : "Stopped";
            leanDebugOutput.appendLine(`[LeanLspClient] state -> ${name} (${newState})`);
        });

        await new Promise<void>((resolve) => {

            if ((leanClientInstance as any).state === 2) return resolve();

            const disp = (leanClientInstance as any).onDidChangeState?.(({ newState }: any) => {
                if (newState === 2) {
                    disp?.dispose?.();
                    resolve();
                }
            });

            if (!disp) resolve();
        });

        leanDebugOutput.appendLine("[LeanLspClient] ready (state=Running)");

        (leanClientInstance as any).onNotification("window/logMessage", (msg: any) => {
            leanDebugOutput.appendLine(`[server window/logMessage] ${JSON.stringify(msg)}`);
        });
        (leanClientInstance as any).onNotification("textDocument/publishDiagnostics", (p: any) => {
            leanDebugOutput.appendLine(`[diagnostics] ${JSON.stringify(p)}`);
        });
        (leanClientInstance as any).onNotification("$/progress", (p: any) => {
            leanDebugOutput.appendLine(`[progress] ${JSON.stringify(p)}`);
        });

    } catch (err) {
        leanDebugOutput.appendLine(`[LeanLspClient] start failed: ${String(err)}`);
    }
}

export async function deactivateLeanClient(): Promise<void> {
    if (!leanClientInstance) return;
    try {
        await leanClientInstance.stop();
        leanClientInstance = undefined;
        leanDebugOutput.appendLine("[LeanLspClient] stopped");
    } catch (err) {
        leanDebugOutput.appendLine(`[LeanLspClient] error stopping: ${String(err)}`);
    }
}

export async function restartLeanClient(context: ExtensionContext): Promise<void> {
    await deactivateLeanClient();
    await activateLeanClient(context);
}