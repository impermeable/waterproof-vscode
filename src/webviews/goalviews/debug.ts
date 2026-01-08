import { Uri } from "vscode";
import { CoqGoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";

//the debug panel extends the GoalsBase class
export class DebugPanel extends GoalsBase {

    //stores information from previous action
    private previousGoal: CoqGoalAnswer<PpString> | undefined;

    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        super(extensionUri, config, "debug");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible) {
                //when the webview is open and visible the information is updated
                this.updateGoals(this.previousGoal);
            }
        });
    }

    //override updateGoals to save the previous goals and activating the panel before posting the goals message
    override updateGoals(goals: CoqGoalAnswer<PpString> | undefined) {
        this.previousGoal = goals;
        this.activatePanel();
        super.updateGoals(goals); //this super function posts the requestGoals message
    }

}
