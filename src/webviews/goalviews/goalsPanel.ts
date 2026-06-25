import { Uri } from "vscode";
import { LspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../waterproofPanel";
import { MessageType } from "../../../shared";
import { GoalsBase } from "./goalsBase";
import { IExecutor } from "../../components";
import { PpString, RocqGoalAnswer } from "../../../lib/types";

//the goals panel extends the GoalsBase class
export class GoalsPanel extends GoalsBase implements IExecutor {
  private previousGoal: RocqGoalAnswer<PpString> | undefined;
  private data: string[] = ["no results"];

  // constructor to define the name and to listen for webview events
  constructor(extensionUri: Uri, config: LspClientConfig) {
    super(extensionUri, config, "goals", true);
    this.on(WebviewEvents.change, () => {
      if (this.state === WebviewState.visible) {
        // TODO: show last goals?
      }
    });
  }

  setResults(results: string[]): void {
    if (results[0] == "createHelp") {
      this.readyPanel();
      this.activatePanel();
      this.revealPanel();
    } else {
      // Set the data property to the provided results
      this.data = results;
      // Send a postMessage to the webview with the MessageType.setData and the data
      this.postMessage({ type: MessageType.setData, body: this.data });
    }
  }
}
