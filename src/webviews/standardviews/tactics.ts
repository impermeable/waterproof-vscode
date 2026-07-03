import { Uri } from "vscode";
import {
  WaterproofPanel,
  WebviewEvents,
  WebviewState,
} from "../waterproofPanel";

// Import the JSON data containing the Rocq tactics
import dataRocq from "../../../completions/tactics.json";
// Import the JSON data for Lean tactics
import dataLean from "../../../completions/tacticsLean.json";
// Import the JSON data for Yalep tactics (Lean files ending in `_yalep.lean`)
import dataYalep from "../../../completions/tacticsYalep.json";
import { CompositeClient } from "../../lsp-client/composite";
import { RocqLspClient } from "../../lsp-client/rocq";
import { LeanLspClient } from "../../lsp-client/lean";
import type { TacticsData } from "../../../shared";

export class TacticsPanel extends WaterproofPanel {
  private lastClient?: RocqLspClient | LeanLspClient;
  private isYalep = false;

  constructor(extensionUri: Uri) {
    // Initialize the tactics panel with the extension Uri and the webview name
    super(extensionUri, "tactics");

    this.readyPanel();
    // Set up an event listener for WebviewEvents.change event
    this.on(WebviewEvents.change, (_e) => {
      switch (
        this.state // Check the state of the webview
      ) {
        // If the webview is open
        case WebviewState.open:
          break;
        // If the webview is ready
        case WebviewState.ready:
          break;
        // If the webview is visible
        case WebviewState.visible:
          break;
        // If the webview is closed
        case WebviewState.closed:
          // Get panel ready
          this.readyPanel();
          break;
      }
    });
  }

  showView(_name: string, data?: TacticsData) {
    if (data) super.showView("tactics", data);
    else if (this.lastClient instanceof LeanLspClient)
      super.showView("tactics", this.isYalep ? dataYalep : dataLean);
    else super.showView("tactics", dataRocq);
  }

  update(client: CompositeClient) {
    if (!client) return;

    const isYalep =
      client.activeDocument?.uri.fsPath.endsWith("_yalep.lean") ?? false;
    if (this.lastClient === client.activeClient && this.isYalep === isYalep)
      return;

    this.lastClient = client.activeClient;
    this.isYalep = isYalep;
    this.showView("tactics");
  }
}
