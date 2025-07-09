import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { MessageType } from "../../../shared";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";
import { WaterproofLogger } from "../../helpers";

//the logbook panel extends the GoalsBase class
export class Logbook extends GoalsBase {

    //array to save messages
    private readonly messages: GoalAnswer<PpString>[] = [];

    // constructor to define the name and to listen for webview events
    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        super(extensionUri, config, "logbook");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible) {
                // when the panel is visible or focused the messages are sent
                this.postMessage({ type: MessageType.renderGoalsList, body: {goalsList: this.messages }});
            }
        });
    }

    //override updateGoals to save the previous message and activating the panel before posting the message
    override updateGoals(goals: GoalAnswer<PpString> | undefined) {
        WaterproofLogger.log(`Logbook: updating goals with ${goals}.`);
        if (!goals) return;
        this.messages.push(goals);
        this.activatePanel();
        this.postMessage({ type: MessageType.renderGoalsList, body: {goalsList: this.messages }});
    }

}
