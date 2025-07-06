import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
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

    //sends message for renderGoals
    updateGoals(goals: GoalAnswer<PpString> | undefined) {
        this.postMessage({ type: MessageType.renderGoals, body: {goals : goals ? [goals] : []} });
    }

    //sends message for errorGoals
    failedGoals(e: unknown) {
        // FIXME: The error `e` should have a proper type instead of `unknown`.
        //        See `updateGoals` in extension.ts, where this `failedGoals`
        //        is called as the result of a Promise rejection.
        this.postMessage({ type: MessageType.errorGoals, body: e});
    }

    //deactivates panel
    disable() {
        this.deactivatePanel();
    }

}
