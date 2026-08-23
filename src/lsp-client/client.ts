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
  CodeAction,
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

  /**
   * Gets code actions for a given diagnostic, filtering out any that are not allowed by `isAllowedCodeAction`.
   * @param document The document for which to get code actions.
   * @param diag The diagnostic for which to get code actions.
   * @param token Cancellation token to cancel the request.
   * @param containingArea The range of the input area containing the diagnostic.
   * @returns A promise resolving to the list of allowed code actions.
   */
  private async resolveCodeActionsFor(
    document: TextDocument,
    diag: Diagnostic,
    token: CancellationToken,
    containingArea: Range,
  ): Promise<OffsetCodeAction[]> {
    const areaStart = document.offsetAt(containingArea.start);
    const areaEnd = document.offsetAt(containingArea.end);

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
      // Ask the LSP for the code actions for the given diagnostic.
      const results = await this.client.sendRequest(
        CodeActionRequest.type,
        params,
        token,
      );
      if (!results) return [];

      const validActions: {
        action: OffsetCodeAction;
        isPreferred?: boolean;
      }[] = [];

      for (const result of results) {
        // Actions support commands as well as edits, but we don't handle those
        if (!("edit" in result) || !result.edit) continue;
        // If the code action is disabled, we skip it.
        if (result.disabled) continue;
        // LSP specific filtering
        if (!this.isAllowedCodeAction(result)) {
          wpl.debug(
            `[resolveCodeActionsFor] skipping disallowed code action "${result.title}"`,
          );
          continue;
        }

        const edit = await p2c.asWorkspaceEdit(result.edit);
        const entries = edit.entries();

        // Applying only part of a multi-document action could corrupt the proof.
        if (
          entries.some(([uri]) => uri.toString() !== document.uri.toString())
        ) {
          continue;
        }

        const edits: OffsetEdit[] = [];
        for (const [, textEdits] of entries) {
          for (const te of textEdits) {
            edits.push({
              start: document.offsetAt(te.range.start),
              end: document.offsetAt(te.range.end),
              newText: te.newText,
            });
          }
        }

        if (edits.length === 0) continue;

        // Reject the whole action if any single edit reaches outside the
        // input area, since we don't want to apply edits that could corrupt
        // the proof state with no recovery
        if (!edits.every((e) => e.start >= areaStart && e.end <= areaEnd)) {
          wpl.debug(
            `[resolveCodeActionsFor] dropped "${result.title}": edit outside input area [${areaStart}, ${areaEnd}]`,
          );
          continue;
        }

        validActions.push({
          action: {
            title: result.title,
            edits,
          },
          isPreferred: result.isPreferred,
        });
      }

      // Only return preferred actions if there are any, otherwise return all valid actions.
      const preferredActions = validActions.filter((a) => a.isPreferred);
      const actionsToReturn =
        preferredActions.length > 0 ? preferredActions : validActions;

      // Limit the number of code actions sent to the editor to 3, to prevent the editor being flooded.
      const keptActions = actionsToReturn.slice(0, 3);
      const droppedActions = actionsToReturn.slice(3);
      if (droppedActions.length > 0) {
        wpl.debug(
          `[resolveCodeActionsFor] dropped ${droppedActions.length} action(s) beyond top 3 ` +
            `for diagnostic "${diag.message}": ${droppedActions
              .map((a) => `"${a.action.title}"`)
              .join(", ")}`,
        );
      }

      return keptActions.map((a) => a.action);
    } catch (e) {
      if (!token.isCancellationRequested) {
        wpl.log(`[LspClient] Failed to resolve code actions: ${e}`);
      }
      return [];
    }
  }

  /**
   * Determines if a code action is allowed to be sent to the editor
   * Can be overridden by other LSP clients to filter out code actions
   * that are not relevant to the editor.
   *
   * @param result The code action to check
   * @returns true if the code action is allowed, false otherwise
   */
  protected isAllowedCodeAction(_result: CodeAction): boolean {
    return true;
  }

  protected async processDiagnostics(): Promise<void> {
    const document = this.activeDocument;
    if (!document) return;

    this.diagnosticsCts?.cancel();
    this.diagnosticsCts?.dispose();
    const cts = new CancellationTokenSource();
    this.diagnosticsCts = cts;
    const token = cts.token;

    const diagnostics = languages.getDiagnostics(document.uri);
    const docVersionAtStart = document.version;

    // Used to bound which code actions are allowed to
    // surface for each diagnostic (see resolveCodeActionsFor).
    // avoids unncessary LSP requests for code actions that would be rejected anyway.
    const inputAreas = this.getInputAreas(document);

    const isStale = (): boolean =>
      token.isCancellationRequested ||
      document.version !== docVersionAtStart ||
      this.activeDocument?.uri.toString() !== document.uri.toString();

    // Build the base diagnostics (no code actions yet) and send them right away,
    // so squiggles/messages show up without waiting on code action resolution.
    const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map((d) => ({
      message: d.message,
      severity: vscodeSeverityToWaterproof(d.severity),
      startOffset: document.offsetAt(d.range.start),
      endOffset: document.offsetAt(d.range.end),
    }));

    wpl.debug(
      `[diag] sending ${positionedDiagnostics.length} base diagnostics, version=${docVersionAtStart}`,
    );

    if (isStale()) {
      if (this.diagnosticsCts === cts) {
        this.diagnosticsCts = undefined;
        cts.dispose();
      }
      return;
    }

    await this.webviewManager!.postAndCacheMessage(document, {
      type: MessageType.diagnostics,
      body: { positionedDiagnostics, version: docVersionAtStart },
    });

    // Resolve code actions per-diagnostic in parallel, but push each one to the
    // webview as soon as *it* resolves instead of waiting for all of them.
    let anyResolved = false;
    try {
      await Promise.all(
        diagnostics.map(async (d, index) => {
          const containingArea = inputAreas?.find((area) =>
            area.contains(d.range),
          );

          const codeActions = containingArea
            ? await this.resolveCodeActionsFor(
                document,
                d,
                token,
                containingArea,
              )
            : [];
          if (codeActions.length === 0 || isStale()) return;

          positionedDiagnostics[index].codeActions = codeActions;
          anyResolved = true;

          wpl.debug(
            `[diag] sending code action patch index=${index} version=${docVersionAtStart} actions=${codeActions.length}`,
          );

          this.webviewManager!.postMessage(document.uri.toString(), {
            type: MessageType.codeActionsResolved,
            body: { version: docVersionAtStart, index, codeActions },
          });
        }),
      );

      // Cache the final message with all code actions so that
      // they remain when we switch tabs.
      if (anyResolved && !isStale()) {
        this.webviewManager!.cacheMessage(document, {
          type: MessageType.diagnostics,
          body: { positionedDiagnostics, version: docVersionAtStart },
        });
      }
    } finally {
      if (this.diagnosticsCts === cts) {
        this.diagnosticsCts = undefined;
        cts.dispose();
      }
    }
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
    const diagnosticsCts = this.diagnosticsCts;
    this.diagnosticsCts = undefined;
    diagnosticsCts?.cancel();
    diagnosticsCts?.dispose();
    this.fileProgressComponents.forEach((c) => c.dispose());
    this.disposables.forEach((d) => d.dispose());
    return this.client.dispose(timeout);
  }
}
