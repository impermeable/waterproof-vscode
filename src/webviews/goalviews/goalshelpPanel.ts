import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";

export class GoalsHelpPanel extends GoalsBase {
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
}
