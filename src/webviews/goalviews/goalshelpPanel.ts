import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { MessageType } from "../../../shared";
import { GoalsBase } from "./goalsBase";
import { IExecutor } from "../../components";

export class GoalsHelpPanel extends GoalsBase implements IExecutor{
  // Initialize the data for the results
  private data: string[] = ['no results'];
  
  private previousGoal: GoalAnswer<PpString> | undefined;

  constructor(extensionUri: Uri, config: CoqLspClientConfig) {
    super(extensionUri, config, "goals-help", true); // new id
    this.on(WebviewEvents.change, (_e) => {
      switch (this.state) { // Check the state of the webview
        // If the webview is visible
        case WebviewState.visible:
          if (this.previousGoal) {
            this.updateGoals(this.previousGoal);
          }
          break;
        // If the webview is closed
        case WebviewState.closed:
          // Get panel ready again
          this.readyPanel()
          break;
      }
    });
  }

  override updateGoals(goals: GoalAnswer<PpString> | undefined) {
    this.previousGoal = goals;
    super.updateGoals(goals);
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
      this.postMessage({ type: MessageType.setData, body: this.data })
    }
  }
}
