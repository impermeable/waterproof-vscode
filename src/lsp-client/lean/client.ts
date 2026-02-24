import { LeanGoalAnswer, LeanGoalRequest } from "../../../lib/types";
import { LspClient } from "../client";
import {
  CancellationTokenSource,
  EventEmitter,
  Position,
  TextDocument,
  Disposable,
  Range,
  OutputChannel,
  SemanticTokens,
} from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { FileProgressParams } from "../requestTypes";
import {
  leanFileProgressNotificationType,
  leanGoalRequestType,
  LeanPublishDiagnosticsParams,
} from "./requestTypes";
import { WaterproofLogger as wpl } from "../../helpers";
import { LanguageClientProvider, WpDiagnostic } from "../clientTypes";
import { WebviewManager } from "../../webviewManager";
import { findOccurrences } from "../qedStatus";
import {
  InputAreaStatus,
  OffsetSemanticToken,
  SemanticTokenType,
} from "@impermeable/waterproof-editor";
import { ServerStoppedReason } from "@leanprover/infoview-api";
import {
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
  SemanticTokensRegistrationType,
} from "vscode-languageclient";
import { MessageType } from "../../../shared";

/**
 * Maps LSP semantic token type strings to our SemanticTokenType enum values.
 * Returns undefined for token types we don't want to highlight.
 */
function mapLspTokenType(lspType: string): SemanticTokenType | undefined {
  switch (lspType) {
    case "variable":
      return SemanticTokenType.Variable;
    case "parameter":
      return SemanticTokenType.Parameter;
    case "function":
    case "method":
      return SemanticTokenType.Function;
    case "type":
    case "class":
    case "interface":
    case "struct":
    case "enum":
      return SemanticTokenType.Type;
    case "namespace":
    case "module":
      return SemanticTokenType.Namespace;
    case "keyword":
      return SemanticTokenType.Keyword;
    case "property":
      return SemanticTokenType.Property;
    default:
      // Pass through unknown types as-is using Variable as fallback.
      // This allows the editor to still display them with a default style.
      return SemanticTokenType.Variable;
  }
}

export class LeanLspClient extends LspClient<LeanGoalRequest, LeanGoalAnswer> {
  language = "lean4";

  constructor(clientProvider: LanguageClientProvider, channel: OutputChannel) {
    super(clientProvider, channel);

    // call each file progress component when the server has processed a part
    this.disposables.push(
      this.client.onNotification(leanFileProgressNotificationType, (params) => {
        this.onFileProgress(params);
      })
    );

    const hndl = this.client.middleware.handleDiagnostics;
    this.client.middleware.handleDiagnostics = (uri, diagnostics_, next) => {
      if (hndl) hndl(uri, diagnostics_, next);

      // diagnostics formatting for infoview
      const c2p = this.client.code2ProtocolConverter;
      const uri_ = c2p.asUri(uri);

      const diagnostics = diagnostics_ as WpDiagnostic[];
      const infoviewDiagnostics = diagnostics.map((d) => ({
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

      this.diagnosticsEmitter.fire({
        uri: uri_,
        diagnostics: infoviewDiagnostics,
      });
    };
  }

  /** Timer for debouncing semantic token requests. */
  private semanticTokenTimer?: NodeJS.Timeout | number;

  protected async onFileProgress(progress: FileProgressParams) {
    if (this.activeDocument?.uri.toString() === progress.textDocument.uri) {
      this.computeInputAreaStatus(this.activeDocument);
      this.requestSemanticTokensDebounced(this.activeDocument);
    }

    super.onFileProgress(progress);
  }

  /**
   * Request semantic tokens from the LSP server after a debounce delay.
   * This avoids flooding the server with requests during rapid progress updates.
   */
  private requestSemanticTokensDebounced(document: TextDocument) {
    if (this.semanticTokenTimer) {
      clearTimeout(this.semanticTokenTimer);
    }
    this.semanticTokenTimer = setTimeout(() => {
      this.requestAndForwardSemanticTokens(document).catch((err) => {
        wpl.debug(`Semantic tokens request failed: ${err}`);
      });
    }, 300);
  }

  /**
   * Requests semantic tokens from the Lean LSP server and forwards them
   * to the editor webview as OffsetSemanticTokens.
   */
  private async requestAndForwardSemanticTokens(
    document: TextDocument
  ): Promise<void> {
    if (!this.client.isRunning() || !this.webviewManager) return;

    // Get the semantic tokens provider via the registered feature
    const feature = this.client.getFeature(
      SemanticTokensRegistrationType.method
    );
    if (!feature) return;

    const provider = feature.getProvider(document);
    if (!provider?.full) return;

    let tokens: SemanticTokens | undefined | null;
    try {
      tokens = await provider.full.provideDocumentSemanticTokens(
        document,
        new CancellationTokenSource().token
      );
    } catch {
      return; // Server busy or request cancelled
    }

    if (!tokens || !tokens.data || tokens.data.length === 0) return;

    // Get the token legend from the server capabilities
    const serverCapabilities = this.client.initializeResult?.capabilities;
    const tokenLegend = serverCapabilities?.semanticTokensProvider?.legend;
    if (!tokenLegend) return;

    const data = tokens.data;
    const offsetTokens: OffsetSemanticToken[] = [];

    let line = 0;
    let char = 0;

    for (let i = 0; i < data.length; i += 5) {
      const deltaLine = data[i];
      const deltaStartChar = data[i + 1];
      const length = data[i + 2];
      const tokenTypeIndex = data[i + 3];
      // data[i + 4] is tokenModifiers (unused for now)

      // Compute absolute position
      if (deltaLine > 0) {
        line += deltaLine;
        char = deltaStartChar;
      } else {
        char += deltaStartChar;
      }

      // Map the token type index to a string via the legend
      const lspTokenType = tokenLegend.tokenTypes[tokenTypeIndex];
      const tokenType = mapLspTokenType(lspTokenType);
      if (!tokenType) continue; // Skip unknown token types

      // Convert line/char to document offset
      const startOffset = document.offsetAt(new Position(line, char));
      const endOffset = startOffset + length;

      offsetTokens.push({ startOffset, endOffset, tokenType });
    }

    // Forward to editor webview
    this.webviewManager.postMessage(document.uri.toString(), {
      type: MessageType.semanticTokens,
      body: { tokens: offsetTokens },
    });
  }

  createGoalsRequestParameters(
    document: TextDocument,
    position: Position
  ): LeanGoalRequest {
    return {
      textDocument: VersionedTextDocumentIdentifier.create(
        document.uri.toString(),
        document.version
      ),
      position: {
        line: position.line,
        character: position.character,
      },
    };
  }

  async requestGoals(
    params?: LeanGoalRequest | Position
  ): Promise<LeanGoalAnswer> {
    if (!params || "line" in params) {
      // if `params` is not a `GoalRequest` ...
      params ??= this.activeCursorPosition;
      if (!this.activeDocument || !params) {
        throw new Error(
          "Cannot request goals; there is no active document and/or cursor position."
        );
      }
      params = this.createGoalsRequestParameters(this.activeDocument, params);
    }
    wpl.debug(
      `Sending request for goals with params: ${JSON.stringify(params)}`
    );
    return this.client.sendRequest(leanGoalRequestType, params);
  }

  async sendViewportHint(
    _document: TextDocument,
    _start: number,
    _end: number
  ): Promise<void> {
    // this is not currently used or supported by Lean
  }

  async startWithHandlers(
    webviewManager: WebviewManager,
    allowedLanguages: string[]
  ): Promise<string[]> {
    const lang = await super.startWithHandlers(
      webviewManager,
      allowedLanguages
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

  protected getInputAreas(document: TextDocument): Range[] | undefined {
    const content = document.getText();

    // find (positions of) opening and closings tags for input areas, and check that they're valid
    const openOffsets = findOccurrences(":::input\n", content);

    return openOffsets.map((openPos) => {
      const closePos = content.indexOf(":::\n", openPos);
      return new Range(
        document.positionAt(openPos),
        document.positionAt(closePos)
      );
    });
  }

  protected async determineProofStatus(
    document: TextDocument,
    inputArea: Range
  ): Promise<InputAreaStatus> {
    const content = document.getText();

    const nextQed = content.indexOf(
      "\nQed\n",
      document.offsetAt(inputArea.start)
    );
    const nextProof = content.indexOf(
      "\nProof:\n",
      document.offsetAt(inputArea.start)
    );

    if (nextProof && nextQed >= nextProof) {
      return InputAreaStatus.Invalid;
    }

    // request goals and return conclusion based on them
    const response = await this.requestGoals(
      this.createGoalsRequestParameters(document, inputArea.end.translate(0, 0))
    );

    return response?.goals.length
      ? InputAreaStatus.Incomplete
      : InputAreaStatus.Proven;
  }

  // Emitters for infoview
  private didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>();
  public didChange(
    cb: (params: DidChangeTextDocumentParams) => void
  ): Disposable {
    return this.didChangeEmitter.event(cb);
  }

  private didCloseEmitter = new EventEmitter<DidCloseTextDocumentParams>();
  public didClose(
    cb: (params: DidCloseTextDocumentParams) => void
  ): Disposable {
    return this.didCloseEmitter.event(cb);
  }

  private diagnosticsEmitter = new EventEmitter<LeanPublishDiagnosticsParams>();
  public diagnostics(
    cb: (params: LeanPublishDiagnosticsParams) => void
  ): Disposable {
    return this.diagnosticsEmitter.event(cb);
  }

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private customNotificationEmitter = new EventEmitter<{
    method: string;
    params: any;
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
