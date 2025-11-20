import {
  ExtensionContext,
  workspace,
  window,
  TextDocument,
  Position,
  OutputChannel,
  commands,
  Uri,
} from "vscode";
import { Trace } from "vscode-languageclient/node";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";
import { AbstractLspClient } from "./abstractLspClient";
import { GoalAnswer, GoalConfig, GoalRequest, PpString } from "../../lib/types";
import { WaterproofLogger as wpl } from "../helpers";
import { version } from "os";
import { WaterproofCompletion } from "@impermeable/waterproof-editor";
import { MessageType } from "../../shared";
import { DocumentSymbol, DocumentSymbolParams, DocumentSymbolRequest } from "vscode-languageclient";


type LC = new (...args: any[]) => any;
const Mixed = AbstractLspClient(LanguageClient as unknown as LC);

interface PlainGoal {
  rendered: string;
  goals: string[];
}

type PlainGoalResult = PlainGoal | null;

export class LeanLspClient extends (Mixed as any) {
  private readonly context: ExtensionContext;

  constructor(
    context: ExtensionContext,
    clientOptions?: LanguageClientOptions
  ) {
    const wpCfg = workspace.getConfiguration("waterproof");
    const configuredLake = (wpCfg.get<string>("lean.lakePath") || "").trim();
    const lakeArgs = wpCfg.get<string[]>("lean.lakeArgs") || ["serve"];
    const legacyLean =
      workspace
        .getConfiguration("lean")
        .get<string>("executablePath")
        ?.trim() || "";

    const serverCommand = configuredLake || legacyLean || "lean";
    const serverArgs = configuredLake ? lakeArgs : ["--server"];

    const serverOptions: ServerOptions = {
      command: serverCommand,
      args: serverArgs,
      options: { env: process.env },
    };

    const lspTraceChannel = window.createOutputChannel("Lean LSP (Trace)");
    lspTraceChannel.show(true);

    const defaultClientOptions: LanguageClientOptions = {
      documentSelector: [
        { language: "lean4", scheme: "file" },
        { language: "lean4", scheme: "untitled" },
        { language: "lean4", scheme: "vscode-local" },
      ],
      outputChannelName: "Lean LSP",
      traceOutputChannel: lspTraceChannel,
      revealOutputChannelOn: 1,
    };
    super(
      "lean",
      "Lean Language Server",
      serverOptions,
      clientOptions ?? defaultClientOptions
    );
    (this as any).trace = Trace.Verbose;
    (this as any).setTrace?.(Trace.Verbose);
  }

  createGoalsRequestParameters(
    document: TextDocument,
    position: Position
  ): GoalRequest {
    return {
      textDocument: { uri: document.uri.toString(), version: document.version },
      position,
    };
  }

  isPosition(x: any): x is Position {
    return x && typeof x.line === "number" && typeof x.character === "number";
  }

  // Implement required abstract methods from AbstractLspClient as minimal stubs.
  // We need each lean client to convert its goal format into GoalAnswer format
  requestGoals(params?: GoalRequest | Position): Promise<GoalAnswer<PpString>> {
    let goalRequest: GoalRequest;
    if (!params) {
      // if `params` is not a `GoalRequest` ...
      if (!this.activeDocument || !this.activeCursorPosition) {
        throw new Error(
          "Cannot request goals; there is no active document and/or cursor position."
        );
      }
      goalRequest = this.createGoalsRequestParameters(
        this.activeDocument,
        this.activeCursorPosition
      );
    } else if (this.isPosition(params)) {
      if (!this.activeDocument) {
        throw new Error("Cannot request goals; there is no active document .");
      }
      goalRequest = this.createGoalsRequestParameters(
        this.activeDocument,
        params
      );
    } else {
      goalRequest = params;
    }
    wpl.debug(
      `Sending request for goals with params: ${JSON.stringify(goalRequest)}`
    );

    let leanParams = {
      textDocument: {
        uri: goalRequest.textDocument.uri,
      },
      position: goalRequest.position,
    };
    return this.sendRequest("$/lean/plainGoal", leanParams).then(
      (result: PlainGoalResult) => {
        wpl.debug("Lean plainGoal result: " + JSON.stringify(result));
        let goalsConfig: GoalConfig<PpString> | undefined = undefined;
        //we now do format conversion
        if (result && result.goals && result.goals.length > 0) {
          const mainGoals = result.goals.map(
            (g) => ({
              hyps: [],
              ty: ["Pp_string", g] as PpString,
            }) /* as Goal<PpString> */
          );

          goalsConfig = {
            goals: mainGoals,
            stack: [],
            shelf: [],
            given_up: [],
            bullet: undefined,
          };
        }

        const ga: GoalAnswer<PpString> = {
          textDocument: goalRequest.textDocument,
          position: goalRequest.position,
          messages: [],
          goals: goalsConfig,
          error: undefined,
        };
        return ga;
      }
    );
  }

  sendViewportHint(
    document: TextDocument,
    start: number,
    end: number
  ): Promise<void> {
    // No viewport hint for Lean in this minimal client.
    return Promise.resolve();
  }

  // Implement other required methods from ILeanLspClient
  async requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]> {

    document ??= this.activeDocument;
    if (!document)
      throw new Error("Cannot request symbols; there is no active document.");

    const params: DocumentSymbolParams = {
      textDocument: { uri: document.uri.toString() }
    };

    const response = await this.sendRequest(DocumentSymbolRequest.type, params);

    if (!response) return [];

    return response as DocumentSymbol[];
  }


  async updateCompletions(document: TextDocument): Promise<void> {
    if (!this.isRunning()) return;
    if (!this.webviewManager?.has(document)) {
      throw new Error(
        "Cannot update completions; no ProseMirror webview is known for " +
        document.uri.toString()
      );
    }
    const pos = this.activeCursorPosition;
    if (!pos) {
      return;
    }
    const params = {
      textDocument: { uri: document.uri.toString() },
      position: pos,
    };
    const call = await this.sendRequest("textDocument/completion", params);
    let items;
    if (Array.isArray(call)) {
      items = call;
    } else if (call && Array.isArray(call.items)) {
      items = call.items;
    } else {
      items = [];
    }
    const completions: WaterproofCompletion[] = items.map((ci: any) => {
      const insertText = ci.textEdit?.newText ?? ci.insertText ?? ci.label;

      return {
        label: ci.label,
        detail: (ci.detail ?? "") as string,
        type: "variable",
        template: insertText,
      };
    });
    this.webviewManager!.postMessage(document.uri.toString(), {
      type: MessageType.setAutocomplete,
      body: completions,
    });
  }
}
/// ---
let leanClientInstance: LeanLspClient | undefined;

let clientRunning: boolean = false;

// lightweight debug output channel
const leanDebugOutput: OutputChannel =
  window.createOutputChannel("Lean LSP Debug");

export function getLeanInstance(): LeanLspClient | undefined {
  return leanClientInstance;
}

export function isLeanClientRunning(): boolean {
  return clientRunning;
}

export async function activateLeanClient(
  context: ExtensionContext
): Promise<void> {
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
      const name =
        newState === 2 ? "Running" : newState === 1 ? "Starting" : "Stopped";
      leanDebugOutput.appendLine(
        `[LeanLspClient] state -> ${name} (${newState})`
      );
    });

    await new Promise<void>((resolve) => {
      if ((leanClientInstance as any).state === 2) return resolve();

      const disp = (leanClientInstance as any).onDidChangeState?.(
        ({ newState }: any) => {
          if (newState === 2) {
            disp?.dispose?.();
            resolve();
          }
        }
      );

      if (!disp) resolve();
    });

    leanDebugOutput.appendLine("[LeanLspClient] ready (state=Running)");

    (leanClientInstance as any).onNotification(
      "window/logMessage",
      (msg: any) => {
        leanDebugOutput.appendLine(
          `[server window/logMessage] ${JSON.stringify(msg)}`
        );
      }
    );
    (leanClientInstance as any).onNotification(
      "textDocument/publishDiagnostics",
      (p: any) => {
        leanDebugOutput.appendLine(`[diagnostics] ${JSON.stringify(p)}`);
      }
    );
    (leanClientInstance as any).onNotification("$/progress", (p: any) => {
      leanDebugOutput.appendLine(`[progress] ${JSON.stringify(p)}`);
    });

    clientRunning = true;
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
    leanDebugOutput.appendLine(
      `[LeanLspClient] error stopping: ${String(err)}`
    );
  }
}

export async function restartLeanClient(
  context: ExtensionContext
): Promise<void> {
  await deactivateLeanClient();
  await activateLeanClient(context);
}
