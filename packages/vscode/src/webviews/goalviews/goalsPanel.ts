import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";

//the goals panel extends the GoalsBase class
export class GoalsPanel extends GoalsBase {

    private previousGoal: GoalAnswer<PpString> | undefined;

    // constructor to define the name and to listen for webview events
    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        super(extensionUri, config, "goals");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible)
                if (this.previousGoal)
                    this.updateGoals(this.previousGoal);  // when the panels is focused or visible the goalsPanel is updated
        });
    }

    //override updateGoals to save the previous goals and activating the panel before posting the goals message
    override updateGoals(goals: GoalAnswer<PpString> | undefined) {
        this.previousGoal = goals;
        super.updateGoals(goals);
    }

}
