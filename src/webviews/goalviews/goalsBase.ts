import { Uri } from "vscode";
import { GoalAnswer, GoalRequest, PpString } from "../../../lib/types";
import { MessageType } from "../../../shared";
import { IGoalsComponent } from "../../components";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { CoqWebview } from "../coqWebview";

//class for panels that need Goals objects from coq-lsp
export abstract class GoalsBase extends CoqWebview implements IGoalsComponent {

    protected config: CoqLspClientConfig;

    constructor(extensionUri: Uri, config: CoqLspClientConfig, name: string) {
        super(extensionUri,name);
        this.config = config;
    }

    //sends message for requestGoals
    goalRequestSent(cursor: GoalRequest) {
        this.postMessage({ type: MessageType.requestGoals, body: cursor});
    }

    //sends message for renderGoals
    updateGoals(goals: GoalAnswer<PpString> | undefined) {
        this.postMessage({ type: MessageType.renderGoals, body: goals});
    }

    //sends message for errorGoals
    failedGoals(e: any) {
        this.postMessage({ type: MessageType.errorGoals, body: e});
    }

    //deactivates panel
    disable() {
        this.deactivatePanel();
    }

}
