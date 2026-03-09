import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { MessageType } from "../../../shared";
import { GoalsBase } from "./goalsBase";
import { IExecutor } from "../../components";

//the goals panel extends the GoalsBase class
export class GoalsPanel extends GoalsBase implements IExecutor {

    private previousGoal: GoalAnswer<PpString> | undefined;
    private data: string[] = ['no results'];

    // constructor to define the name and to listen for webview events
    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        super(extensionUri, config, "goals", true);
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
