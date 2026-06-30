import { LeanGoalAnswer, LeanGoalRequest } from "../../../lib/types";
import { LspClient } from "../client";
import {
  EventEmitter,
  extensions,
  Position,
  TextDocument,
  Disposable,
  Range,
  OutputChannel,
  Diagnostic,
  DiagnosticSeverity,
  workspace,
} from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { FileProgressParams } from "../requestTypes";
import {
  LeanDiagnostic,
  leanFileProgressNotificationType,
  leanGoalRequestType,
  LeanPublishDiagnosticsParams,
  LeanTag,
} from "./requestTypes";
import {
  WaterproofConfigHelper,
  WaterproofLogger as wpl,
  WaterproofSetting,
} from "../../helpers";
import { LanguageClientProvider, WpDiagnostic } from "../clientTypes";
import { WebviewManager } from "../../webviewManager";
import { findOccurrences } from "../qedStatus";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { ServerStoppedReason } from "@leanprover/infoview-api";
import {
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
} from "vscode-languageclient";
import { FileProgressKind, MessageType } from "../../../shared";
import { patchDiagnosticConverters } from "./converter";

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
  language = "lean4";

  /**
   * Whether the Lean server is still processing the document.
   * Used to avoid marking a proof as complete before checking has finished.
   */
  private isBusy: boolean = true;

  constructor(clientProvider: LanguageClientProvider, channel: OutputChannel) {
    super(clientProvider, channel);

    patchDiagnosticConverters(
      this.client.protocol2CodeConverter,
      this.client.code2ProtocolConverter,
    );

    // call each file progress component when the server has processed a part
    this.disposables.push(
      this.client.onNotification(leanFileProgressNotificationType, (params) => {
        this.onFileProgress(params);
      }),
    );

    const hndl = this.client.middleware.handleDiagnostics;
    this.client.middleware.handleDiagnostics = (uri, diagnostics_, next) => {
      const diagnostics = diagnostics_ as WpDiagnostic[];
      // Find the document these diagnostics actually belong to
      const document = workspace.textDocuments.find(
        (d) => d.uri.toString() === uri.toString(),
      );
      const inputAreas = document ? this.getInputAreas(document) : [];
      const friendlyDiagnostics = this.rewriteDiagnostics(
        diagnostics,
        inputAreas,
      );

      if (hndl) hndl(uri, friendlyDiagnostics, next);

      // diagnostics formatting for infoview
      const c2p = this.client.code2ProtocolConverter;
      const uri_ = c2p.asUri(uri);

      const infoviewDiagnostics = friendlyDiagnostics.map((d) => ({
        ...c2p.asDiagnostic(d),
        ...(d.data?.sentenceRange
          ? {
              range: {
                start: d.data.sentenceRange.start,
                end: d.data.sentenceRange.end,
              },
            }
          : {}),
      }));

      wpl.debug(
        `[leanClient] handleDiagnostics uri=${uri_.split("/").pop()}, count=${infoviewDiagnostics.length}, diags=${JSON.stringify(infoviewDiagnostics.map((d) => ({ range: d.range, msg: d.message?.substring(0, 40) })))}`,
      );
      this.diagnosticsEmitter.fire({
        uri: uri_,
        diagnostics: infoviewDiagnostics,
      });
    };
  }

  /**
   * Rewrites diagnostics to be more user-friendly,
   * e.g. by chaning the "unsolved goals" message to not be a wall of scary text.
   * @param diagnostics The diagnostics to rewrite.
   * @param inputAreas The input areas in the document
   * @returns The rewritten diagnostics.
   */
  private rewriteDiagnostics(
    diagnostics: WpDiagnostic[],
    inputAreas: Range[],
  ): WpDiagnostic[] {
    return diagnostics.map((d) => {
      if ((d as LeanDiagnostic).leanTags?.includes(LeanTag.UnsolvedGoals)) {
        const isInsideInputArea = inputAreas.some((area) => {
          const intersection = area.intersection(d.range);
          return intersection !== undefined && !intersection.isEmpty;
        });
        if (isInsideInputArea) {
          // rewrite unsolved goals messages inside input areas to be more user-friendly
          return {
            ...d,
            message: `(Sub)proof starting on line ${d.range.start.line + 1} is not finished yet.`,
          };
        }
      }
      return d;
    });
  }

  async prelaunchChecks(): Promise<string[]> {
    if (extensions.getExtension("leanprover.lean4")) {
      wpl.log("Lean 4 extension detected, skipping Waterproof Lean client.");
      return [];
    }

    const lakePath = WaterproofConfigHelper.get(WaterproofSetting.LakePath);
    if (!lakePath) {
      wpl.log("Lean prelaunch check failed: lakePath is empty.");
      return [];
    }

    const command = `${lakePath} --version`;
    const ok = await this.execReturnsOk(command);
    return ok ? [this.language] : [];
  }

  private async execReturnsOk(command: string): Promise<boolean> {
    wpl.log(`Running command: ${command}`);
    return new Promise((resolve) => {
      // eslint-disable-next-line @typescript-eslint/no-require-imports
      const { exec } = require("child_process");
      exec(command, (err: { message?: string } | null) => {
        if (err) {
          const message = err.message ?? "Unknown error";
          wpl.log(`Lean prelaunch check failed: ${message}`);
          resolve(false);
        } else {
          resolve(true);
        }
      });
    });
  }

  protected onFileProgress(progress: FileProgressParams) {
    // Call super first so LSP ranges are converted to VSCode Ranges before we store/use them.
    super.onFileProgress(progress);

    if (this.activeDocument?.uri.toString() === progress.textDocument.uri) {
      // --- busy-indicator (Lean edition) ---
      // Find the first processing range, where we want to add the busy-indicator to.
      const firstProcessing = progress.processing.find(
        (p) => p.kind === undefined || p.kind === FileProgressKind.Processing,
      );
      if (firstProcessing && this.webviewManager) {
        if (!this.isBusy) {
          wpl.debug(
            `[leanClient.onFileProgress] isBusy false -> true (processing range starting at ` +
              `line ${firstProcessing.range.start.line})`,
          );
        }
        this.isBusy = true;
        const { line, character } = firstProcessing.range.start;
        const from = this.activeDocument.offsetAt(
          new Position(line, character),
        );
        const to = this.activeDocument.offsetAt(
          new Position(
            firstProcessing.range.end.line,
            firstProcessing.range.end.character,
          ),
        );

        // Send message to add the busy indicator
        this.webviewManager.postMessage(progress.textDocument.uri, {
          type: MessageType.executionInfo,
          body: { from, to },
        });
      } else {
        if (this.isBusy) {
          wpl.debug(
            `[leanClient.onFileProgress] isBusy true -> false (no processing ranges remain)`,
          );
        }
        this.isBusy = false;
      }
      wpl.debug(
        `[leanClient.onFileProgress] progress for active doc; ` +
          `processingRanges=${progress.processing.length}, isBusy=${this.isBusy}; ` +
          `recomputing input area status`,
      );
      this.computeInputAreaStatus(this.activeDocument);
    }
  }

  createGoalsRequestParameters(
    document: TextDocument,
    position: Position,
  ): LeanGoalRequest {
    return {
      textDocument: VersionedTextDocumentIdentifier.create(
        document.uri.toString(),
        document.version,
      ),
      position: {
        line: position.line,
        character: position.character,
      },
    };
  }

  async requestGoals(
    params?: LeanGoalRequest | Position,
  ): Promise<LeanGoalAnswer | null> {
    if (!params || "line" in params) {
      // if `params` is not a `GoalRequest` ...
      params ??= this.activeCursorPosition;
      if (!this.activeDocument || !params) {
        throw new Error(
          "Cannot request goals; there is no active document and/or cursor position.",
        );
      }
      params = this.createGoalsRequestParameters(this.activeDocument, params);
    }
    wpl.debug(
      `Sending request for goals with params: ${JSON.stringify(params)}`,
    );
    return this.client.sendRequest(leanGoalRequestType, params);
  }

  async sendViewportHint(
    _document: TextDocument,
    _start: number,
    _end: number,
  ): Promise<void> {
    // this is not currently used or supported by Lean
  }

  async startWithHandlers(
    webviewManager: WebviewManager,
    allowedLanguages: string[],
  ): Promise<string[]> {
    const lang = await super.startWithHandlers(
      webviewManager,
      allowedLanguages,
    );

    // Allows for any custom notifications to be handled by
    // forwarding to a custom notification emitter

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const starHandler = (method: string, params_: any) => {
      this.customNotificationEmitter.fire({ method, params: params_ });
    };
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    this.client.onNotification(starHandler as any, () => {});
    return lang;
  }

  protected getInputAreas(document: TextDocument): Range[] {
    const content = document.getText();

    // find (positions of) opening and closings tags for input areas, and check that they're valid
    const openOffsets = findOccurrences(":::input\n", content);

    const inputAreas = openOffsets.map((openPos) => {
      const closePos = content.indexOf(":::\n", openPos);
      return new Range(
        document.positionAt(openPos),
        document.positionAt(closePos),
      );
    });

    wpl.debug(
      `[leanClient.getInputAreas] doc=${document.uri.toString().split("/").pop()}, ` +
        `':::input\\n' openOffsets=${JSON.stringify(openOffsets)}, ` +
        `found ${inputAreas.length} input area(s): ${JSON.stringify(
          inputAreas.map((a) => ({
            start: { line: a.start.line, ch: a.start.character },
            end: { line: a.end.line, ch: a.end.character },
          })),
        )}`,
    );

    return inputAreas;
  }

  protected async determineProofStatus(
    document: TextDocument,
    inputArea: Range,
    diags: Array<Diagnostic>,
    lowerBound: Position,
  ): Promise<InputAreaStatus> {
    wpl.debug(
      `[leanClient.determineProofStatus] called for inputArea ` +
        `start=(${inputArea.start.line},${inputArea.start.character}) ` +
        `end=(${inputArea.end.line},${inputArea.end.character}), ` +
        `lowerBound=(${lowerBound.line},${lowerBound.character}), ` +
        `isBusy=${this.isBusy}, totalDiags=${diags.length}`,
    );

    // If Lean hasn't finished processing up to the end of this input area, an empty goals
    // response simply means "not checked yet" rather than "proof complete".  Guard against
    // that to prevent the bar from turning green prematurely (e.g. while typing "We ap" or
    // when the proof has invalid syntax like "Help\n• Fix a : ℝ\n" without a closing Qed).
    if (this.isBusy) {
      wpl.debug(
        `[leanClient.determineProofStatus] -> Incorrect (server still busy, status undetermined)`,
      );
      return InputAreaStatus.Incorrect;
    }

    // Get diagnostics that intersect with the input area, and check if any of them are error-level.
    const diagsInArea = diags.filter((v) => {
      const intersection = inputArea.intersection(v.range);
      return intersection !== undefined && !intersection.isEmpty;
    });

    // If there are any error-level diagnostics inside the input area, the proof is wrong.
    // This catches cases like an incomplete tactic keyword (e.g. just "We") which can make
    // Lean report empty goals at the query position while still being invalid.
    const hasErrorDiagnostic = diagsInArea.some(
      (d) => d.severity === DiagnosticSeverity.Error,
    );
    wpl.debug(
      `[leanClient.determineProofStatus] diagsInArea=${diagsInArea.length}, ` +
        `hasErrorDiagnostic=${hasErrorDiagnostic}, ` +
        `diagsInArea=${JSON.stringify(
          diagsInArea.map((d) => ({
            severity: d.severity,
            range: {
              start: { line: d.range.start.line, ch: d.range.start.character },
              end: { line: d.range.end.line, ch: d.range.end.character },
            },
            msg: d.message?.substring(0, 60),
          })),
        )}`,
    );
    if (hasErrorDiagnostic) {
      wpl.debug(
        `[leanClient.determineProofStatus] -> Incorrect (error-level diagnostic inside input area)`,
      );
      return InputAreaStatus.Incorrect;
    }

    // The proof's closing marker (`□` in Yalep, `QED` in Verbose Lean) lives in a `lean`
    // block *after* the input area's closing `:::`. In these dialects the marker is an active
    // step that discharges the final goal, so proof completion must be measured at the marker
    // rather than at `inputArea.end` (which would still show an open goal for a finished
    // proof). This mirrors the Rocq client, which queries goals at the `Qed.` after the input
    // area. If no marker is present, the proof isn't closed and the area is incorrect.
    const markerPosition = this.findProofEndPosition(document, inputArea.end);
    if (!markerPosition) {
      wpl.debug(
        `[leanClient.determineProofStatus] -> Incorrect (no closing marker '□'/'QED' after input area)`,
      );
      return InputAreaStatus.Incorrect;
    }

    const goalsParams = this.createGoalsRequestParameters(
      document,
      markerPosition,
    );
    const response = await this.requestGoals(goalsParams);

    wpl.debug(
      `[leanClient.determineProofStatus] goals requested at marker position ` +
        `(${markerPosition.line},${markerPosition.character}), ` +
        `response=${response ? `present, goals.length=${response.goals.length}` : "null"}, ` +
        `goals=${response ? JSON.stringify(response.goals) : "n/a"}`,
    );

    if (!response) {
      wpl.debug(
        `[leanClient.determineProofStatus] -> Incorrect (no goals response)`,
      );
      return InputAreaStatus.Incorrect;
    }

    // return incorrect if there are still goals remaining
    if (response.goals.length > 0) {
      wpl.debug(
        `[leanClient.determineProofStatus] -> Incorrect (${response.goals.length} goal(s) remaining)`,
      );
      return InputAreaStatus.Incorrect;
    }

    // Goals are empty, proof looks complete, but check for sorry
    // The Lean LSP prefixes all sorry-like aliases with "declaration uses " including hint
    // Important: when hint suggests something that immediatly resolves the goal,
    // it will not throw a sorry warning. It will see the proof as valid.
    const SORRY_PREFIX = "declaration uses ";

    const hasSorry = diags.some(
      (d) =>
        d.severity === DiagnosticSeverity.Warning &&
        d.range.start.isAfter(lowerBound) &&
        d.range.start.isBeforeOrEqual(inputArea.end) &&
        d.message.startsWith(SORRY_PREFIX),
    );
    const status = hasSorry ? InputAreaStatus.Invalid : InputAreaStatus.Correct;
    wpl.debug(
      `[leanClient.determineProofStatus] no goals remaining; hasSorry=${hasSorry} -> ${status}`,
    );
    return status;
  }

  /**
   * Finds the position just after the proof-closing marker (`□` in Yalep, `QED` in Verbose
   * Lean) that follows `searchFrom` in the document. In these dialects the marker lives in a
   * `lean` block *after* the input area's closing `:::`, and it is the step that discharges
   * the final goal — so proof completion must be measured here rather than at the input-area
   * boundary. Returns the earliest marker's end position, or `undefined` when no marker is
   * present (i.e. the proof isn't closed yet).
   */
  private findProofEndPosition(
    document: TextDocument,
    searchFrom: Position,
  ): Position | undefined {
    const content = document.getText();
    const fromOffset = document.offsetAt(searchFrom);

    // Bound the search to before the next input area, so an unclosed proof can't borrow the
    // closing marker of a later proof (which would falsely mark this area complete).
    const nextInputArea = content.indexOf(":::input\n", fromOffset);
    const searchLimit = nextInputArea >= 0 ? nextInputArea : content.length;

    const markers = ["□", "QED"];
    let bestStart: number | undefined;
    let bestLength = 0;
    for (const marker of markers) {
      const idx = content.indexOf(marker, fromOffset);
      if (idx >= 0 && idx < searchLimit && (bestStart === undefined || idx < bestStart)) {
        bestStart = idx;
        bestLength = marker.length;
      }
    }

    return bestStart === undefined
      ? undefined
      : document.positionAt(bestStart + bestLength);
  }

  // Emitters for infoview
  private didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>();
  public didChange(
    cb: (params: DidChangeTextDocumentParams) => void,
  ): Disposable {
    return this.didChangeEmitter.event(cb);
  }

  private didCloseEmitter = new EventEmitter<DidCloseTextDocumentParams>();
  public didClose(
    cb: (params: DidCloseTextDocumentParams) => void,
  ): Disposable {
    return this.didCloseEmitter.event(cb);
  }

  private diagnosticsEmitter = new EventEmitter<LeanPublishDiagnosticsParams>();
  public diagnostics(
    cb: (params: LeanPublishDiagnosticsParams) => void,
  ): Disposable {
    return this.diagnosticsEmitter.event(cb);
  }

  private customNotificationEmitter = new EventEmitter<{
    method: string;
    params: any; // eslint-disable-line @typescript-eslint/no-explicit-any
  }>();

  /** Fires whenever a custom notification (i.e. one not defined in LSP) is received. */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  public customNotification(cb: (params: any) => void): Disposable {
    return this.customNotificationEmitter.event(cb);
  }

  private clientStoppedEmitter = new EventEmitter<ServerStoppedReason>();
  public clientStopped = this.clientStoppedEmitter.event;

  async dispose(timeout?: number): Promise<void> {
    await super.dispose(timeout);
    this.clientStoppedEmitter.fire({
      message: "Lean server has stopped",
      reason: "",
    });
  }
}
