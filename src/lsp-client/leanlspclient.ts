import {
  Disposable,
  ExtensionContext,
  EventEmitter,
  workspace,
  window,
  TextDocument,
  Position,
  OutputChannel,
  languages,
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
import { WaterproofCompletion } from "@impermeable/waterproof-editor";
import { MessageType } from "../../shared";
import { DocumentSymbol, DocumentSymbolParams, DocumentSymbolRequest, FeatureClient, Middleware } from "vscode-languageclient";
import { WebviewManager } from "../webviewManager";

type LC = new (...args: any[]) => FeatureClient<Middleware, LanguageClientOptions> & {
  dispose(timeout?: number): Promise<void>;
};
const Mixed = AbstractLspClient(LanguageClient as LC);

interface PlainGoal {
  rendered: string;
  goals: string[];
}

type PlainGoalResult = PlainGoal | null;

export class LeanLspClient extends (Mixed) {
  private readonly context: ExtensionContext;

  private _patchedSendNotification = false;

  private didChangeEmitter = new EventEmitter<any>();
  private didCloseEmitter = new EventEmitter<any>();
  private diagnosticsEmitter = new EventEmitter();

  public didChange(cb: (params: any) => void): Disposable {
    return this.didChangeEmitter.event(cb);
  }
  public didClose(cb: (params: any) => void): Disposable {
    return this.didCloseEmitter.event(cb);
  }

  private patchSendNotificationOnce() {
    if (this._patchedSendNotification) return;
    this._patchedSendNotification = true;

    const orig = (this as any).sendNotification.bind(this);

    (this as any).sendNotification = async (method: string, params: any) => {
      // outgoing LSP notifications
      if (method === "textDocument/didChange") this.didChangeEmitter.fire(params);
      if (method === "textDocument/didClose") this.didCloseEmitter.fire(params);

      return orig(method, params);
    };
  }

  private readonly _serverEmitters = new Map<string, EventEmitter<any>>();
  private readonly _serverHooked = new Set<string>();

  private ensureServerHook(method: string) {
    if (this._serverHooked.has(method)) return;
    this._serverHooked.add(method);
    // FIX: move this firing to middleware.handleDiagnostics
    // (this as any).onNotification(method, (params: any) => {
    //   this._serverEmitters.get(method)?.fire(params);
    // });
  }

  public diagnostics(cb: (params: any) => void): Disposable {
    const method = "textDocument/publishDiagnostics";
    let em = this._serverEmitters.get(method);
    if (!em) {
      em = new EventEmitter<any>();
      this._serverEmitters.set(method, em);
    }
    this.ensureServerHook(method);
    return em.event(cb);
  }

  public customNotificationFor(method: string, cb: (params: any) => void): Disposable {
    let em = this._serverEmitters.get(method);
    if (!em) {
      em = new EventEmitter<any>();
      this._serverEmitters.set(method, em);
    }
    this.ensureServerHook(method);
    return em.event(cb);
  }


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
    this.context = context;
    this.diagnosticsCollection = languages.createDiagnosticCollection("lean4");
    this.patchSendNotificationOnce();
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
        wpl.debug("=== LEAN GOALS DEBUG ===");
        wpl.debug("Full result object: " + JSON.stringify(result, null, 2));
        wpl.debug("Result is null?: " + (result === null));
        if (result) {
          wpl.debug("result.rendered: " + result.rendered);
          wpl.debug("result.goals: " + JSON.stringify(result.goals));
          wpl.debug("result.goals length: " + (result.goals?.length || 0));
        }

        let goalsConfig: GoalConfig<PpString> | undefined = undefined;

        // Try to parse goals - check both goals array and rendered string
        if (result) {
          // If goals array exists and has items, use it
          if (result.goals && result.goals.length > 0) {
            wpl.debug("Using goals array: " + result.goals.length + " goals");
            const mainGoals = result.goals.map(
              (g) => ({
                hyps: [],
                ty: ["Pp_string", g] as PpString,
              })
            );

            goalsConfig = {
              goals: mainGoals,
              stack: [],
              shelf: [],
              given_up: [],
              bullet: undefined,
            };
          }
          // If no goals array but rendered exists, try using rendered
          else if (result.rendered && result.rendered.trim().length > 0) {
            wpl.debug("No goals array, but rendered exists. Using rendered string.");
            wpl.debug("Rendered content: " + result.rendered);

            const mainGoals = [{
              hyps: [],
              ty: ["Pp_string", result.rendered] as PpString,
            }];

            goalsConfig = {
              goals: mainGoals,
              stack: [],
              shelf: [],
              given_up: [],
              bullet: undefined,
            };
          } else {
            wpl.debug("No goals or rendered content found in result");
          }
        } else {
          wpl.debug("Result is null - no goals available");
        }

        const ga: GoalAnswer<PpString> = {
          textDocument: goalRequest.textDocument,
          position: goalRequest.position,
          messages: [],
          goals: goalsConfig,
          error: undefined,
        };

        wpl.debug("Final GoalAnswer goals?: " + (ga.goals ? "YES" : "NO"));
        wpl.debug("=== END LEAN GOALS DEBUG ===");

        return ga;
      }
    ).catch((error) => {
      wpl.debug("ERROR in Lean goals request: " + error);
      throw error;
    });
  }

  getViewportNotificationName(): string {
    return "$/lean/viewRange";
  }
  async startWithHandlers(webviewManager: WebviewManager): Promise<void> {
    this.webviewManager = webviewManager;

    // Set up document change listener for Lean files
    this.disposables.push(workspace.onDidChangeTextDocument(event => {
      if (event.document.languageId.startsWith('lean') &&
        webviewManager.has(event.document.uri.toString())) {

        // Get cursor position from the change event
        if (event.contentChanges.length > 0) {
          const change = event.contentChanges[0];
          // The cursor is at the end of the change
          const cursorPos = change.range.end;

          // Update the active cursor position
          this.activeCursorPosition = cursorPos;
          this.activeDocument = event.document;
        }

        this.updateCompletions(event.document);
      }
    }));

    await super.startWithHandlers(webviewManager);
    this.patchSendNotificationOnce();
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
    console.log("LEAN updateCompletions called for :", document.uri.toString(), "lang:", document.languageId);
    if (!this.isRunning()) {
      console.log("LEAN client not running")
      return;
    }
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
    console.log("Lean sending autocompletions")
    this.webviewManager!.postMessage(document.uri.toString(), {
      type: MessageType.setAutocomplete,
      body: completions,
    });
  }

}
/// ---
let leanClientInstance: LeanLspClient | undefined;

// lightweight debug output channel
const leanDebugOutput: OutputChannel =
  window.createOutputChannel("Lean LSP Debug");



export async function activateLeanClient(
  context: ExtensionContext
): Promise<void> {
  if (leanClientInstance) return;

  leanDebugOutput.show(true);
  leanDebugOutput.appendLine("[LeanLspClient] activateLeanClient()");

  try {
    leanClientInstance = new LeanLspClient(context, undefined);
    context.subscriptions.push(leanDebugOutput);

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

  
    // (leanClientInstance as any).onNotification(
    //   "window/logMessage",
    //   (msg: any) => {
    //     leanDebugOutput.appendLine(
    //       `[server window/logMessage] ${JSON.stringify(msg)}`
    //     );
    //   }
    // );
    // (leanClientInstance as any).onNotification(
    //   "textDocument/publishDiagnostics",
    //   (p: any) => {
    //     leanDebugOutput.appendLine(`[diagnostics] ${JSON.stringify(p)}`);
    //   }
    // );
    // (leanClientInstance as any).onNotification("$/progress", (p: any) => {
    //   leanDebugOutput.appendLine(`[progress] ${JSON.stringify(p)}`);
    // });

    // clientRunning = true;
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
