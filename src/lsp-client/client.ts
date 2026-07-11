import {
  Position,
  TextDocument,
  Range,
  OutputChannel,
  languages,
  workspace,
  Disposable,
  DiagnosticSeverity,
  Diagnostic,
  CancellationToken,
  CancellationTokenSource,
} from "vscode";
import {
  CodeActionParams,
  CodeActionRequest,
  DocumentSymbol,
  DocumentSymbolParams,
  DocumentSymbolRequest,
  LogTraceNotification,
  SymbolInformation,
} from "vscode-languageclient";
import { SentenceManager } from "./sentenceManager";
import { IFileProgressComponent } from "../components";
import { WebviewManager } from "../webviewManager";
import {
  qualifiedSettingName,
  WaterproofConfigHelper,
  WaterproofSetting,
  WaterproofLogger as wpl,
} from "../helpers";

import {
  InputAreaStatus,
  OffsetCodeAction,
  OffsetDiagnostic,
  OffsetEdit,
  Severity,
  WaterproofCompletion,
} from "@impermeable/waterproof-editor";
import { convertToSimple, FileProgressParams } from "./requestTypes";
import { MessageType, SimpleProgressParams } from "../../shared";
import {
  ILspClient,
  LanguageClient,
  LanguageClientProvider,
  WpDiagnostic,
} from "./clientTypes";
import { GoalAnswer, GoalRequest } from "../../lib/types";

function vscodeSeverityToWaterproof(severity: DiagnosticSeverity): Severity {
  switch (severity) {
    case DiagnosticSeverity.Error:
      return Severity.Error;
    case DiagnosticSeverity.Warning:
      return Severity.Warning;
    case DiagnosticSeverity.Information:
      return Severity.Information;
    case DiagnosticSeverity.Hint:
      return Severity.Hint;
  }
}

function wasCanceledByServer(reason: unknown): boolean {
  return (
    !!reason &&
    typeof reason === "object" &&
    "message" in reason &&
    reason.message === "Request got old in server"
  ); // or: code == -32802
}

export abstract class LspClient<
  GoalRequestT extends GoalRequest,
  GoalAnswerT extends GoalAnswer,
> implements ILspClient {
  private _client?: LanguageClient;

  /**
   * Gets the underlying VS Code language client.
   * Initializes one if necessary.
   */
  get client(): LanguageClient {
    if (this._client === undefined) {
      wpl.log(`${this.language} client not running, initializing`);
      this._client = this.provideClient();
    }
    return this._client;
  }

  /**
   * Checks whether the underlying client exists and is running.
   */
  isRunning(): boolean {
    if (this._client === undefined) return false;
    return this._client.isRunning();
  }

  /**
   * Run any pre-launch checks before starting this client.
   */
  async prelaunchChecks(): Promise<string[]> {
    return this.language ? [this.language] : [];
  }

  /**
   * Language identifier of this client, e.g. 'rocq' or 'lean4'
   */
  readonly language: string | undefined;

  /**
   * Resources that must be released upon disposal of this client.
   */
  readonly disposables: Disposable[] = [];

  detailedErrors: boolean = false;

  activeDocument: TextDocument | undefined;
  activeCursorPosition: Position | undefined;

  /**
   * The object that keeps track of the (end) positions of the sentences in `activeDocument`.
   */
  readonly sentenceManager: SentenceManager;
  protected readonly fileProgressComponents: IFileProgressComponent[] = [];

  webviewManager: WebviewManager | undefined;

  /**
   * Whether we are using viewport based checking.
   */
  readonly viewPortBasedChecking: boolean = !WaterproofConfigHelper.get(
    WaterproofSetting.ContinuousChecking,
  );
  /**
   * The range of the current viewport.
   */
  viewPortRange: Range | undefined = undefined;

  /*
   * Constructs a Waterproof language client.
   */
  constructor(
    private readonly provideClient: LanguageClientProvider,
    protected readonly lspOutputChannel: OutputChannel,
  ) {
    this.sentenceManager = new SentenceManager();

    // forward progress notifications to editor
    this.fileProgressComponents.push({
      dispose() {
        /* noop */
      },
      onProgress: (params) => {
        const document = this.activeDocument;
        if (!document) return;
        const body: SimpleProgressParams = {
          numberOfLines: document.lineCount,
          progress: params.processing.map(convertToSimple),
        };
        this.webviewManager!.postAndCacheMessage(document, {
          type: MessageType.progress,
          body,
        });
      },
    });

    // deduce (end) positions of sentences from progress notifications
    this.fileProgressComponents.push(this.sentenceManager);
    const diagnosticsCollection = languages.createDiagnosticCollection(
      this.language,
    );

    // Set detailedErrors to the value of the `Waterproof.detailedErrorsMode` setting.
    this.detailedErrors = WaterproofConfigHelper.get(
      WaterproofSetting.DetailedErrorsMode,
    );
    // Update `detailedErrors` when the setting changes.
    this.disposables.push(
      workspace.onDidChangeConfiguration((e) => {
        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.DetailedErrorsMode),
          )
        ) {
          this.detailedErrors = WaterproofConfigHelper.get(
            WaterproofSetting.DetailedErrorsMode,
          );
        }

        // When the LogDebugStatements setting changes we update the logDebug boolean in the WaterproofLogger class.
        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.LogDebugStatements),
          )
        ) {
          wpl.logDebug = WaterproofConfigHelper.get(
            WaterproofSetting.LogDebugStatements,
          );
        }
      }),
    );

    // send diagnostics to editor (for squiggly lines)
    this.client.middleware.handleDiagnostics = (uri, diagnostics_) => {
      // Note: Here we typecast diagnostics_ to WpDiagnostic[], the new type includes the custom data field
      //      added by coq-lsp required for the line long error mode.
      if (!this.detailedErrors) {
        const diagnostics = diagnostics_ as WpDiagnostic[];
        diagnosticsCollection.set(
          uri,
          diagnostics.map((d) => {
            const start = d.data?.sentenceRange?.start ?? d.range.start;
            const end = d.data?.sentenceRange?.end ?? d.range.end;
            return {
              ...d,
              range: new Range(start, end),
            };
          }),
        );
      } else {
        diagnosticsCollection.set(uri, diagnostics_);
      }
    };

    this.disposables.push(
      languages.onDidChangeDiagnostics((e) => {
        if (this.activeDocument === undefined) return;
        // Comparing the uris (by doing uris.includes(this.activeDocument.uri)) does not seem to achieve
        // the same result.
        if (
          e.uris.map((uri) => uri.path).includes(this.activeDocument.uri.path)
        ) {
          this.processDiagnostics();
        }
      }),
    );

    // send proof statuses to editor when document checking is done
    this.disposables.push(
      this.client.onNotification(LogTraceNotification.type, (params) => {
        // Print `params.message` to custom lsp output channel
        this.lspOutputChannel.appendLine(params.message);

        if (params.message.includes("document fully checked")) {
          this.onCheckingCompleted();
        }
      }),
    );
  }

  protected onFileProgress(params: FileProgressParams): void {
    // convert LSP range to VSC range
    params.processing.forEach((fp): void => {
      fp.range = this.client.protocol2CodeConverter.asRange(fp.range);
    });
    // notify each component
    this.fileProgressComponents.forEach((c) => c.onProgress(params));
  }

  private async resolveCodeActionsFor(
    document: TextDocument,
    diag: Diagnostic,
    token: CancellationToken,
  ): Promise<OffsetCodeAction[]> {
    if (diag.severity === DiagnosticSeverity.Error) return [];

    const c2p = this.client.code2ProtocolConverter;
    const p2c = this.client.protocol2CodeConverter;

    const params: CodeActionParams = {
      textDocument: { uri: document.uri.toString() },
      range: c2p.asRange(diag.range),
      context: {
        diagnostics: await c2p.asDiagnostics([diag]),
      },
    };

    try {
      // Passing the token means an in-flight request is aborted (and rejects here)
      // as soon as a newer diagnostics pass supersedes this one, instead of running
      // to completion in the background only to have its result discarded.
      const results = await this.client.sendRequest(
        CodeActionRequest.type,
        params,
        token,
      );
      if (!results) return [];

      const actions: OffsetCodeAction[] = [];
      for (const result of results) {
        if (!("edit" in result) || !result.edit) continue;

        // asWorkspaceEdit normalizes both the `changes` and `documentChanges` forms of
        // a LSP WorkspaceEdit into one iterable - some servers only populate
        // `documentChanges`, so this must not be replaced with manual `changes[uri]`
        // access or those edits are silently dropped.
        const edit = await p2c.asWorkspaceEdit(result.edit);

        const edits: OffsetEdit[] = [];

        // Now 'edit' is a fully parsed native vscode.WorkspaceEdit
        for (const [uri, textEdits] of edit.entries()) {
          if (uri.toString() !== document.uri.toString()) continue;

          for (const te of textEdits) {
            edits.push({
              start: document.offsetAt(te.range.start),
              end: document.offsetAt(te.range.end),
              newText: te.newText,
            });
          }
        }

        if (edits.length > 0) {
          actions.push({ title: result.title, edits });
        }
      }
      return actions;
    } catch (e) {
      // Cancellation (LSP RequestCancelled = -32800) is expected whenever a newer
      // diagnostics pass supersedes this one; don't spam the log for that case.
      if (!token.isCancellationRequested) {
        wpl.log(`[LspClient] Failed to resolve code actions: ${e}`);
      }
      console.log("[LspClient] Cancel");
      return [];
    }
  }

  protected async processDiagnostics(): Promise<void> {
    const document = this.activeDocument;
    if (!document) return;

    // Cancel any code-action resolution still in flight from a previous call - its
    // result would be stale by the time it resolves anyway.
    this.diagnosticsCts?.cancel();
    this.diagnosticsCts?.dispose();
    const cts = new CancellationTokenSource();
    this.diagnosticsCts = cts;
    const token = cts.token;

    const diagnostics = languages.getDiagnostics(document.uri);
    const docVersionAtStart = document.version;
    console.time("processDiagnostics");
    const positionedDiagnostics: OffsetDiagnostic[] = await Promise.all(
      diagnostics.map(async (d) => {
        const codeActions = await this.resolveCodeActionsFor(
          document,
          d,
          token,
        );
        return {
          message: d.message,
          severity: vscodeSeverityToWaterproof(d.severity),
          startOffset: document.offsetAt(d.range.start),
          endOffset: document.offsetAt(d.range.end),
          ...(codeActions.length > 0 ? { codeActions } : {}),
        };
      }),
    );
    console.timeEnd("processDiagnostics");

    // Guard against the document having changed, or this pass having been superseded
    // by a newer one, while we were awaiting resolveCodeActionsFor.
    if (
      token.isCancellationRequested ||
      document.version !== docVersionAtStart
    ) {
      return;
    }

    this.webviewManager!.postAndCacheMessage(document, {
      type: MessageType.diagnostics,
      body: { positionedDiagnostics, version: document.version },
    });
  }

  protected async onCheckingCompleted(): Promise<void> {
    // ensure there is an active document
    const document = this.activeDocument;
    if (!document) {
      wpl.debug(
        `[onCheckingCompleted] 'document fully checked' received but no active document`,
      );
      return;
    }
    wpl.debug(
      `[onCheckingCompleted] 'document fully checked' for ` +
        `${document.uri.toString().split("/").pop()}; recomputing input area status`,
    );

    // send message to ProseMirror editor that checking is done
    // (in addition to LSP message that indicates last Markdown is still being processed)
    this.webviewManager!.postAndCacheMessage(document.uri.toString(), {
      type: MessageType.progress,
      body: { numberOfLines: document.lineCount, progress: [] },
    });

    this.computeInputAreaStatus(document);
  }

  protected abstract determineProofStatus(
    document: TextDocument,
    inputArea: Range,
    diagnostics: Array<Diagnostic>,
    lowerBound: Position,
  ): Promise<InputAreaStatus>;

  protected abstract getInputAreas(document: TextDocument): Range[] | undefined;

  // This setTimeout creates a NodeJS.Timeout object, but in the browser it is just a number.
  computeInputAreaStatusTimer?: NodeJS.Timeout | number;

  /**
   * Tracks the most recent in-flight `processDiagnostics` pass so it can be cancelled
   * when a newer one supersedes it (e.g. the user keeps typing while code actions are
   * still being resolved against the previous diagnostics snapshot).
   */
  private diagnosticsCts?: CancellationTokenSource;

  protected async computeInputAreaStatus(
    document: TextDocument,
  ): Promise<void> {
    if (this.computeInputAreaStatusTimer) {
      clearTimeout(this.computeInputAreaStatusTimer);
    }
    // Computing where all the input areas are requires a fair bit of work,
    // so we add a debounce delay to this function to avoid recomputing on every keystroke.
    this.computeInputAreaStatusTimer = setTimeout(async () => {
      // get input areas based on tags
      const inputAreas = this.getInputAreas(document);
      if (!inputAreas) {
        wpl.debug(
          `[computeInputAreaStatus] getInputAreas returned undefined for ` +
            `${document.uri.toString()} -> illegal input areas`,
        );
        throw new Error("Cannot check proof status; illegal input areas.");
      }

      const diags = languages.getDiagnostics(document.uri);

      wpl.debug(
        `[computeInputAreaStatus] doc=${document.uri.toString().split("/").pop()}, ` +
          `inputAreas=${inputAreas.length}, diagnostics=${diags.length}, ` +
          `viewPortBasedChecking=${this.viewPortBasedChecking}, ` +
          `viewPortRange=${this.viewPortRange ? JSON.stringify({ start: { line: this.viewPortRange.start.line, ch: this.viewPortRange.start.character }, end: { line: this.viewPortRange.end.line, ch: this.viewPortRange.end.character } }) : "undefined"}`,
      );

      // for each input area, check the proof status
      try {
        const statuses = await Promise.all(
          inputAreas.map((area, i) => {
            // compute lower bound for this input area: end of previous input area, or (0, 0) for the first one
            const lowerBound =
              i === 0 ? new Position(0, 0) : inputAreas[i - 1].end;

            if (
              this.viewPortBasedChecking &&
              this.viewPortRange &&
              area.intersection(this.viewPortRange) === undefined
            ) {
              // This input area is outside of the range that has been checked and thus we can't determine its status
              return Promise.resolve(InputAreaStatus.OutOfView);
            }

            return this.determineProofStatus(document, area, diags, lowerBound);
          }),
        );

        wpl.debug(
          `[computeInputAreaStatus] computed statuses for ` +
            `doc=${document.uri.toString().split("/").pop()}: ${JSON.stringify(statuses)} ` +
            `(sending qedStatus message to editor)`,
        );

        // forward statuses to corresponding ProseMirror editor
        this.webviewManager!.postAndCacheMessage(document, {
          type: MessageType.qedStatus,
          body: statuses,
        });
      } catch (reason) {
        if (wasCanceledByServer(reason)) return; // we've likely already sent new requests
        console.log(
          "[computeInputAreaStatus] The catch block caught an error that we don't classify as 'cancelled by server':",
          reason,
        );
      }
    }, 250);
  }

  async startWithHandlers(
    webviewManager: WebviewManager,
    allowedLanguages: string[],
  ): Promise<string[]> {
    if (!this.language || !allowedLanguages.includes(this.language)) {
      return [];
    }

    this.webviewManager = webviewManager;

    // after every document change, request symbols and send completions to the editor
    this.disposables.push(
      workspace.onDidChangeTextDocument((event) => {
        if (
          webviewManager.has(event.document.uri.toString()) &&
          event.document.languageId === this.language
        ) {
          this.updateCompletions(event.document);
        }
      }),
    );

    wpl.debug(`Starting ${this.language} client...`);
    await this.client.start();
    return [this.language ?? "unknown"];
  }

  /**
   * Creates parameter object for a goals request.
   */
  abstract createGoalsRequestParameters(
    document: TextDocument,
    position: Position,
  ): GoalRequestT;

  /** Sends an LSP request with the specified parameters to retrieve the goals. */
  abstract requestGoals(parameters: GoalRequestT): Promise<GoalAnswerT | null>;
  /** Sends an LSP request to retrieve the goals at `position` in the active document. */
  abstract requestGoals(position: Position): Promise<GoalAnswerT | null>;
  /** Sends an LSP request to retrieve the goals at the active cursor position. */
  abstract requestGoals(): Promise<GoalAnswerT | null>;

  async requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]> {
    // use active document if no document is given
    document ??= this.activeDocument;
    if (!document) {
      throw new Error("Cannot request symbols; there is no active document.");
    }

    // send "documentSymbol" request and wait for response
    const params: DocumentSymbolParams = {
      textDocument: {
        uri: document.uri.toString(),
      },
    };
    const response = await this.client.sendRequest(
      DocumentSymbolRequest.type,
      params,
    );

    // convert `response` to array of `DocumentSymbol` (if necessary) and return it
    if (!response) {
      console.error("Response to 'textDocument/documentSymbol' was `null`.");
      return [];
    } else if (response.length === 0 || "range" in response[0]) {
      return response as DocumentSymbol[];
    } else {
      return (response as SymbolInformation[]).map((s) => ({
        name: s.name,
        kind: s.kind,
        tags: s.tags,
        range: s.location.range,
        selectionRange: s.location.range,
      }));
    }
  }

  abstract sendViewportHint(
    document: TextDocument,
    start: number,
    end: number,
  ): Promise<void>;

  async updateCompletions(document: TextDocument): Promise<void> {
    if (!this.client.isRunning()) return;
    if (!this.webviewManager?.has(document)) {
      throw new Error(
        "Cannot update completions; no Waterproof webview is known for " +
          document.uri.toString(),
      );
    }

    // request symbols for `document`
    let symbols: DocumentSymbol[];
    try {
      symbols = await this.requestSymbols(document);
    } catch (reason) {
      if (wasCanceledByServer(reason)) return; // we've likely already sent a new request
      throw reason;
    }

    // convert symbols to completions
    const completions: WaterproofCompletion[] = symbols.map((s) => ({
      label: s.name,
      detail: s.detail?.toLowerCase() ?? "",
      type: "variable",
      template: s.name,
    }));

    // send completions to (all code blocks in) the document's editor (not cached!)
    this.webviewManager.postMessage(document.uri.toString(), {
      type: MessageType.setAutocomplete,
      body: completions,
    });
  }

  dispose(timeout?: number): Promise<void> {
    this.diagnosticsCts?.cancel();
    this.diagnosticsCts?.dispose();
    this.fileProgressComponents.forEach((c) => c.dispose());
    this.disposables.forEach((d) => d.dispose());
    return this.client.dispose(timeout);
  }
}
