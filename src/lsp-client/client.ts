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
  OffsetDiagnostic,
  OffsetMessageSegment,
  Severity,
  WaterproofCompletion,
} from "@impermeable/waterproof-editor";
import { convertToSimple, FileProgressParams } from "./requestTypes";
import { MessageType, SimpleProgressParams } from "../../shared";
import {
  ILspClient,
  LanguageClient,
  LanguageClientProvider,
  MessageSegment,
  SegmentedDiagnostic,
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
 * Identifies a diagnostic, both to match segmented diagnostics to published ones and to
 * carry segments over to the next pass.
 */
function diagnosticKey(
  d: Pick<OffsetDiagnostic, "startOffset" | "endOffset" | "message">,
): string {
  return `${d.startOffset}:${d.endOffset}:${d.message}`;
}

function toPosition(p: { line: number; character: number }): Position {
  return new Position(p.line, p.character);
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
   * Splits the messages of diagnostics into segments, some of which are suggestions with an
   * edit (e.g. Lean's "Try this"). Clients that don't implement this get no suggestions.
   *
   * @param document The document the diagnostics belong to.
   * @param diagnostics The (non-empty) diagnostics of the document.
   * @param token Cancelled when a newer diagnostics pass starts.
   * @returns The segmented diagnostics, which are matched to `diagnostics` by range and
   *   message, or `undefined` if they could not be resolved (in which case the segments of
   *   the previous pass are kept).
   */
  protected resolveMessageSegments?(
    document: TextDocument,
    diagnostics: readonly Diagnostic[],
    token: CancellationToken,
  ): Promise<SegmentedDiagnostic[] | undefined>;

  /** Converts message segments to offset-based segments. */
  private toOffsetSegments(
    document: TextDocument,
    text: string,
    segments: readonly MessageSegment[],
  ): OffsetMessageSegment[] {
    return segments.map(({ text: segmentText, edit }) => {
      if (!edit) return { text: segmentText };
      const start = document.offsetAt(toPosition(edit.range.start));
      const end = document.offsetAt(toPosition(edit.range.end));
      return {
        text: segmentText,
        edit: {
          start,
          end,
          newText: edit.newText,
          oldText: text.slice(start, end),
        },
      };
    });
  }

  /**
   * Sends the diagnostics of the active document to its editor. When the client resolves
   * message segments, the diagnostics are sent again once their segments are known.
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
    const version = document.version;
    const text = document.getText();

    // Carry over the segments of the previous pass for diagnostics that are still there, as
    // long as their edits still apply to the current text. This keeps them visible across
    // progressive diagnostics updates while they are re-resolved.
    const previous = this.resolvedSegments.get(uri);
    const stillApplies = (segments: readonly OffsetMessageSegment[]) =>
      segments.every(
        ({ edit: e }) => !e || text.slice(e.start, e.end) === e.oldText,
      );
    const positionedDiagnostics: OffsetDiagnostic[] = diagnostics.map((d) => {
      const positioned: OffsetDiagnostic = {
        message: d.message,
        severity: vscodeSeverityToWaterproof(d.severity),
        startOffset: document.offsetAt(d.range.start),
        endOffset: document.offsetAt(d.range.end),
      };
      const carried = previous?.get(diagnosticKey(positioned));
      return carried && stillApplies(carried)
        ? { ...positioned, segments: carried }
        : positioned;
    });

    try {
      // Send the diagnostics right away, so squiggles/messages show up without waiting
      // on segment resolution.
      this.webviewManager!.postAndCacheMessage(document, {
        type: MessageType.diagnostics,
        body: { positionedDiagnostics, version },
      });

      if (!this.resolveMessageSegments || diagnostics.length === 0) return;

      let resolved: SegmentedDiagnostic[] | undefined;
      try {
        resolved = await this.resolveMessageSegments(
          document,
          diagnostics,
          token,
        );
      } catch (e) {
        if (!token.isCancellationRequested) {
          wpl.log(`[LspClient] Failed to resolve message segments: ${e}`);
        }
        return;
      }
      if (
        resolved === undefined ||
        token.isCancellationRequested ||
        document.version !== version
      ) {
        return;
      }

      const segmentsByKey = new Map<string, OffsetMessageSegment[]>();
      for (const d of resolved) {
        const key = diagnosticKey({
          startOffset: document.offsetAt(toPosition(d.range.start)),
          endOffset: document.offsetAt(toPosition(d.range.end)),
          message: d.message,
        });
        segmentsByKey.set(
          key,
          this.toOffsetSegments(document, text, d.segments),
        );
      }
      this.resolvedSegments.set(uri, segmentsByKey);

      const withSegments = positionedDiagnostics.map(
        ({ segments: _carried, ...d }): OffsetDiagnostic => {
          const segments = segmentsByKey.get(diagnosticKey(d));
          return segments ? { ...d, segments } : d;
        },
      );
      const changed = withSegments.some(
        (d, i) =>
          JSON.stringify(d.segments) !==
          JSON.stringify(positionedDiagnostics[i].segments),
      );
      if (!changed) return;

      wpl.debug(`[diag] sending diagnostics with segments, version=${version}`);
      this.webviewManager!.postAndCacheMessage(document, {
        type: MessageType.diagnostics,
        body: { positionedDiagnostics: withSegments, version },
      });
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
   * be cancelled when a newer one supersedes it (e.g. the user keeps typing while
   * segments are still being resolved against the previous diagnostics snapshot).
   */
  private readonly diagnosticsCts = new Map<string, CancellationTokenSource>();

  /**
   * Per document URI, the segments of the latest diagnostics pass, keyed by
   * {@linkcode diagnosticKey}. Used to carry them over to the next pass.
   */
  private readonly resolvedSegments = new Map<
    string,
    Map<string, OffsetMessageSegment[]>
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
    this.resolvedSegments.clear();
    this.fileProgressComponents.forEach((c) => c.dispose());
    this.disposables.forEach((d) => d.dispose());
    return this.client.dispose(timeout);
  }
}
