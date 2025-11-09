import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";
import { IExecutor } from "../../components";

export class GoalsHelpPanel extends GoalsBase implements IExecutor{
  // Initialize the data for the results
  private data: string[] = ['no results'];
  
  private previousGoal: GoalAnswer<PpString> | undefined;

  constructor(extensionUri: Uri, config: CoqLspClientConfig) {
    super(extensionUri, config, "goals-help"); // new id
    this.on(WebviewEvents.change, () => {
      if (this.state === WebviewState.visible && this.previousGoal) {
        this.updateGoals(this.previousGoal);
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
