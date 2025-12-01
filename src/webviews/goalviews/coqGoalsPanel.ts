import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";

// Renamed from GoalsPanel to CoqGoalsPanel
export class CoqGoalsPanel extends GoalsBase {

    protected previousGoal: GoalAnswer<PpString> | undefined;

    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        // We still pass "goals" as the name, as this is the underlying ID used by the webview manager
        super(extensionUri, config, "goals");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible)
                if (this.previousGoal)
                    this.updateGoals(this.previousGoal);
        });
    }

    override updateGoals(goals: GoalAnswer<PpString> | undefined) {
        this.previousGoal = goals;
        super.updateGoals(goals);
    }

}