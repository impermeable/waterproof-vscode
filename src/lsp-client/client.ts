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

/**
 * Identifies a diagnostic across diagnostics passes, for carrying code actions over.
 */
function codeActionKey(d: OffsetDiagnostic): string {
  return `${d.startOffset}:${d.endOffset}:${d.message}`;
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
   * Whether the underlying client has been created.
   *
   * Unlike `isRunning`, reading this never creates one, and it stays true for a
   * client that was created but failed to start. Such a client still owns
   * resources that have to be released — in the web build, the worker its
   * server runs in.
   */
  get hasClient(): boolean {
    return this._client !== undefined;
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
          this.processDiagnostics().catch((e) =>
            wpl.log(`[LspClient] Failed to process diagnostics: ${e}`),
          );
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
   * Whether this client asks its language server for code actions to attach to diagnostics.
   *
   * This is opt-in: when enabled, every diagnostic inside an input area costs a request on
   * every diagnostics update, and the resulting actions are shown to students as buttons, so
   * a client should only enable it together with a suitable `isAllowedCodeAction` filter.
   */
  protected readonly requestsCodeActions: boolean = false;

  /** The maximum number of code actions shown for a single diagnostic. */
  private static readonly MAX_CODE_ACTIONS_PER_DIAGNOSTIC = 3;

  /** The maximum number of code action requests in flight at once, per diagnostics pass. */
  private static readonly MAX_CONCURRENT_CODE_ACTION_REQUESTS = 4;

  /**
   * Gets code actions for a given diagnostic, filtering out any that are not allowed by `isAllowedCodeAction`.
   * @param document The document for which to get code actions.
   * @param diag The diagnostic for which to get code actions.
   * @param token Cancellation token to cancel the request.
   * @param containingArea The range of the input area containing the diagnostic.
   * @returns A promise resolving to the list of allowed code actions, or `undefined` if they
   *   could not be retrieved (e.g. because the request failed or was cancelled).
   */
  private async resolveCodeActionsFor(
    document: TextDocument,
    diag: Diagnostic,
    token: CancellationToken,
    containingArea: Range,
  ): Promise<OffsetCodeAction[] | undefined> {
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

      const text = document.getText();
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
            const start = document.offsetAt(te.range.start);
            const end = document.offsetAt(te.range.end);
            edits.push({
              start,
              end,
              newText: te.newText,
              // Lets the editor (and later passes) check that the edit still applies.
              oldText: text.slice(start, end),
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

      return actionsToReturn.map((a) => a.action);
    } catch (e) {
      if (!token.isCancellationRequested) {
        wpl.log(`[LspClient] Failed to resolve code actions: ${e}`);
      }
      return undefined;
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

  /**
   * Whether code actions should be requested for diagnostics: the client has to opt in
   * (see {@linkcode requestsCodeActions}) and the server has to support them.
   */
  private codeActionsEnabled(): boolean {
    return (
      this.requestsCodeActions &&
      !!this.client.initializeResult?.capabilities.codeActionProvider
    );
  }

  /**
   * Sends the diagnostics of the active document to its editor, and then resolves and
   * streams in the code actions for the diagnostics inside input areas.
   */
  protected async processDiagnostics(): Promise<void> {
    const document = this.activeDocument;
    if (!document) return;
    const uri = document.uri.toString();

    // A newer pass for the same document supersedes any pass still in flight.
    const previousCts = this.diagnosticsCts.get(uri);
    previousCts?.cancel();
    previousCts?.dispose();
    const cts = new CancellationTokenSource();
    this.diagnosticsCts.set(uri, cts);
    const token = cts.token;

    const diagnostics = languages.getDiagnostics(document.uri);
    const docVersionAtStart = document.version;

    // Note that switching to another document does not make a pass stale: its results are
    // still posted to (and cached for) the editor of the document they belong to.
    const isStale = (): boolean =>
      token.isCancellationRequested || document.version !== docVersionAtStart;

    const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map((d) => ({
      message: d.message,
      severity: vscodeSeverityToWaterproof(d.severity),
      startOffset: document.offsetAt(d.range.start),
      endOffset: document.offsetAt(d.range.end),
    }));

    try {
      const codeActionsEnabled = this.codeActionsEnabled();

      // Only diagnostics inside an input area get code actions (see resolveCodeActionsFor).
      // This avoids unnecessary LSP requests for code actions that would be rejected anyway.
      const inputAreas = codeActionsEnabled
        ? this.getInputAreas(document)
        : undefined;
      const containingAreas = diagnostics.map((d) =>
        inputAreas?.find((area) => area.contains(d.range)),
      );
      const requested = containingAreas.flatMap((area, index) =>
        area ? [index] : [],
      );

      // Carry over the code actions of the previous pass for diagnostics that are still
      // there, as long as their edits still apply to the current text. This keeps the
      // actions visible across progressive diagnostics updates while they are re-resolved.
      const previousActions = this.resolvedCodeActions.get(uri);
      const currentActions = new Map<string, OffsetCodeAction[]>();
      this.resolvedCodeActions.set(uri, currentActions);
      if (previousActions && requested.length > 0) {
        const text = document.getText();
        for (const index of requested) {
          const d = positionedDiagnostics[index];
          const key = codeActionKey(d);
          const carried = previousActions
            .get(key)
            ?.filter((action) =>
              action.edits.every(
                (e) =>
                  e.oldText !== undefined &&
                  text.slice(e.start, e.end) === e.oldText,
              ),
            );
          if (carried && carried.length > 0) {
            d.codeActions = carried;
            currentActions.set(key, carried);
          }
        }
      }

      wpl.debug(
        `[diag] sending ${positionedDiagnostics.length} base diagnostics, version=${docVersionAtStart}`,
      );

      // Send the diagnostics right away, so squiggles/messages show up without waiting
      // on code action resolution. A copy is sent, since the entries are updated below.
      this.webviewManager!.postAndCacheMessage(document, {
        type: MessageType.diagnostics,
        body: {
          positionedDiagnostics: positionedDiagnostics.map((d) => ({ ...d })),
          version: docVersionAtStart,
        },
      });

      if (requested.length === 0) return;

      // Some servers (e.g. Lean's "Try this" provider) return every action on the lines a
      // diagnostic covers, so the same action can be returned for several diagnostics. It is
      // only shown on the narrowest requested diagnostic that overlaps its edits.
      const ownerOf = (action: OffsetCodeAction): number | undefined => {
        const start = Math.min(...action.edits.map((e) => e.start));
        const end = Math.max(...action.edits.map((e) => e.end));
        let owner: number | undefined;
        for (const index of requested) {
          const d = positionedDiagnostics[index];
          if (d.startOffset > end || start > d.endOffset) continue;
          const width = d.endOffset - d.startOffset;
          if (
            owner === undefined ||
            width <
              positionedDiagnostics[owner].endOffset -
                positionedDiagnostics[owner].startOffset
          ) {
            owner = index;
          }
        }
        return owner;
      };

      let anyChanged = false;
      const resolveOne = async (index: number) => {
        const resolved = await this.resolveCodeActionsFor(
          document,
          diagnostics[index],
          token,
          containingAreas[index]!,
        );
        if (resolved === undefined || isStale()) return;

        const owned = resolved.filter((action) => {
          const owner = ownerOf(action);
          return owner === undefined || owner === index;
        });
        const max = LspClient.MAX_CODE_ACTIONS_PER_DIAGNOSTIC;
        const codeActions = owned.slice(0, max);
        if (owned.length > max) {
          wpl.debug(
            `[resolveCodeActionsFor] dropped ${owned.length - max} action(s) beyond top ${max} ` +
              `for diagnostic "${diagnostics[index].message}": ${owned
                .slice(max)
                .map((a) => `"${a.title}"`)
                .join(", ")}`,
          );
        }

        const diagnostic = positionedDiagnostics[index];
        // Nothing to report: no actions now, and none were carried over from the previous pass.
        if (codeActions.length === 0 && diagnostic.codeActions === undefined)
          return;

        const key = codeActionKey(diagnostic);
        if (codeActions.length > 0) {
          diagnostic.codeActions = codeActions;
          currentActions.set(key, codeActions);
        } else {
          delete diagnostic.codeActions;
          currentActions.delete(key);
        }
        anyChanged = true;

        wpl.debug(
          `[diag] sending code action patch index=${index} version=${docVersionAtStart} actions=${codeActions.length}`,
        );

        this.webviewManager!.postMessage(uri, {
          type: MessageType.codeActionsResolved,
          body: { version: docVersionAtStart, index, codeActions },
        });
      };

      // Resolve code actions per diagnostic, a few at a time, and push each one to the
      // webview as soon as *it* resolves instead of waiting for all of them.
      const queue = [...requested];
      const worker = async () => {
        while (queue.length > 0 && !isStale()) await resolveOne(queue.shift()!);
      };
      await Promise.all(
        Array.from(
          {
            length: Math.min(
              LspClient.MAX_CONCURRENT_CODE_ACTION_REQUESTS,
              queue.length,
            ),
          },
          worker,
        ),
      );

      // Cache the final message with all code actions so that
      // they remain when we switch tabs.
      if (anyChanged && !isStale()) {
        this.webviewManager!.cacheMessage(document, {
          type: MessageType.diagnostics,
          body: { positionedDiagnostics, version: docVersionAtStart },
        });
      }
    } finally {
      if (this.diagnosticsCts.get(uri) === cts) {
        this.diagnosticsCts.delete(uri);
      }
      cts.dispose();
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
   * Tracks, per document URI, the most recent in-flight `processDiagnostics` pass so it can
   * be cancelled when a newer one supersedes it (e.g. the user keeps typing while code
   * actions are still being resolved against the previous diagnostics snapshot).
   */
  private readonly diagnosticsCts = new Map<string, CancellationTokenSource>();

  /**
   * Per document URI, the code actions of the latest diagnostics pass, keyed by
   * {@linkcode codeActionKey}. Used to carry actions over to the next pass.
   */
  private readonly resolvedCodeActions = new Map<
    string,
    Map<string, OffsetCodeAction[]>
  >();

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
    for (const cts of this.diagnosticsCts.values()) {
      cts.cancel();
      cts.dispose();
    }
    this.diagnosticsCts.clear();
    this.resolvedCodeActions.clear();
    this.fileProgressComponents.forEach((c) => c.dispose());
    this.disposables.forEach((d) => d.dispose());
    return this.client.dispose(timeout);
  }
}
