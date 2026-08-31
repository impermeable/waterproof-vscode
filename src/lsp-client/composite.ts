import { LeanLspClient } from "./lean";
import { RocqLspClient } from "./rocq";
import { convertToString } from "../../lib/types";
import { ILspClient, LanguageClientSetups } from "./clientTypes";
import { WaterproofLogger as wpl } from "../helpers";
import { ExtensionContext, Position, TextDocument } from "vscode";
import { DocumentSymbol } from "vscode-languageserver-types";
import { Hypothesis } from "../api";
import { WebviewManager } from "../webviewManager";

export class CompositeClient implements ILspClient {
  public readonly rocqClient: RocqLspClient;
  /**
   * The Lean client, or `undefined` when Lean is not supported by this build
   * (e.g. the web extension, which has no way to spawn a Lake process).
   */
  public readonly leanClient?: LeanLspClient;
  protected readonly lastClient: RocqLspClient | LeanLspClient;

  protected document?: TextDocument;

  constructor(clients: LanguageClientSetups, context: ExtensionContext) {
    this.rocqClient = new RocqLspClient(
      clients.rocq.provider,
      clients.rocq.createOutputChannel(),
      context,
    );
    // Constructing a client eagerly instantiates its underlying `LanguageClient`
    // and its output channel, so only do so for the languages this build
    // actually supports.
    this.leanClient = clients.lean
      ? new LeanLspClient(
          clients.lean.provider,
          clients.lean.createOutputChannel(),
        )
      : undefined;

    this.lastClient = this.rocqClient;
  }

  set activeDocument(document: TextDocument) {
    this.document = document;
    this.activeClient.activeDocument = document;
  }

  set activeCursorPosition(position: Position | undefined) {
    this.activeClient.activeCursorPosition = position;
  }

  get activeDocument(): TextDocument | undefined {
    return this.document;
  }

  get activeCursorPosition(): Position | undefined {
    return this.activeClient.activeCursorPosition;
  }

  get activeClient(): RocqLspClient | LeanLspClient {
    if (!this.activeDocument) return this.lastClient;

    return this.getClient(this.activeDocument);
  }

  protected getClient(document: TextDocument): RocqLspClient | LeanLspClient {
    if (document?.languageId === "lean4" && this.leanClient)
      return this.leanClient;
    else return this.rocqClient;
  }

  updateCompletions(document: TextDocument): Promise<void> {
    return this.getClient(document).updateCompletions(document);
  }

  sendViewportHint(document: TextDocument, start: number, end: number) {
    this.getClient(document).sendViewportHint(document, start, end);
  }

  /**
   * Request the goals for the current document and cursor position.
   */
  public async goals(): Promise<{
    currentGoal: string;
    hypotheses: Array<Hypothesis>;
    otherGoals: string[];
  }> {
    const client = this.activeClient;
    if (!client.activeDocument || !client.activeCursorPosition) {
      throw new Error("No active document or cursor position.");
    }

    const document = client.activeDocument;
    const position = client.activeCursorPosition;

    const params = client.createGoalsRequestParameters(document, position);

    if (client instanceof LeanLspClient) {
      const goalResponse = await client.requestGoals(params);

      if (goalResponse?.goals === undefined) {
        throw new Error("Response contained no goals.");
      }

      return {
        currentGoal: goalResponse.goals[0],
        hypotheses: [],
        otherGoals: goalResponse.goals.slice(1),
      };
    } else {
      const goalResponse = await client.requestGoals(params);

      if (goalResponse.goals === undefined) {
        throw new Error("Response contained no goals.");
      }

      // Convert goals and hypotheses to strings
      const goalsAsStrings = goalResponse.goals.goals.map((g) =>
        convertToString(g.ty),
      );
      // Note: only taking hypotheses from the first goal
      const hyps = goalResponse.goals.goals[0].hyps.map((h) => {
        return {
          name: convertToString(h.names[0]),
          content: convertToString(h.ty),
        };
      });

      return {
        currentGoal: goalsAsStrings[0],
        hypotheses: hyps,
        otherGoals: goalsAsStrings.slice(1),
      };
    }
  }

  requestSymbols(document?: TextDocument): Promise<DocumentSymbol[]> {
    return this.activeClient.requestSymbols(document);
  }

  async prelaunchChecks(): Promise<string[]> {
    const [rocqAllowed, leanAllowed] = await Promise.all([
      this.rocqClient.prelaunchChecks(),
      this.leanClient?.prelaunchChecks() ?? [],
    ]);

    return [...rocqAllowed, ...leanAllowed];
  }

  /**
   * Check if all clients are running.
   */
  isRunning(): boolean {
    return (
      this.rocqClient.isRunning() || (this.leanClient?.isRunning() ?? false)
    );
  }

  async startWithHandlers(
    webviewManager: WebviewManager,
    allowedLanguages: string[],
  ): Promise<string[]> {
    const leanClient = this.leanClient;
    const rocqAllowed = allowedLanguages.includes(this.rocqClient.language);
    const leanAllowed =
      leanClient !== undefined &&
      allowedLanguages.includes(leanClient.language);

    if (!rocqAllowed) {
      wpl.log("Skipping Rocq client start: prelaunch checks failed.");
    }
    if (leanClient === undefined) {
      wpl.log("Skipping Lean client start: Lean is not supported.");
    } else if (!leanAllowed) {
      wpl.log("Skipping Lean client start: prelaunch checks failed.");
    }

    const rocqStart = rocqAllowed
      ? this.rocqClient
          .startWithHandlers(webviewManager, allowedLanguages)
          .catch((err) => {
            wpl.log(`Failed to start Rocq client: ${err}`);
            return [];
          })
      : Promise.resolve([]);

    const leanStart = leanAllowed
      ? leanClient
          .startWithHandlers(webviewManager, allowedLanguages)
          .catch((err) => {
            wpl.log(`Failed to start Lean client: ${err}`);
            return [];
          })
      : Promise.resolve([]);

    return Promise.all([rocqStart, leanStart]).then(
      ([rocqLangs, leanLangs]) => [...rocqLangs, ...leanLangs],
    );
  }

  async dispose(timeout?: number): Promise<void> {
    const disposePromises = [];
    if (this.rocqClient.isRunning()) {
      disposePromises.push(this.rocqClient.dispose(timeout));
    }
    if (this.leanClient?.isRunning()) {
      disposePromises.push(this.leanClient.dispose(timeout));
    }
    await Promise.all(disposePromises);
  }
}
