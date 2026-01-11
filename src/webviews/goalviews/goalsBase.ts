import { Uri } from "vscode";
import { CoqGoalAnswer, PpString } from "../../../lib/types";
import { MessageType } from "../../../shared";
import { IGoalsComponent } from "../../components";
import { LspClientConfig } from "../../lsp-client/clientTypes";
import { CoqWebview } from "../coqWebview";
import { WaterproofConfigHelper, WaterproofSetting } from "../../helpers";
import { CoqLspClient } from "../../lsp-client/coq";
import { WaterproofLogger as wpl } from "../../helpers";

//class for panels that need Goals objects from coq-lsp
export abstract class GoalsBase extends CoqWebview implements IGoalsComponent {

    protected config: LspClientConfig;

    constructor(extensionUri: Uri, config: LspClientConfig, name: string) {
        super(extensionUri,name);
        this.config = config;
    }

    getGoals(client: CoqLspClient): Promise<CoqGoalAnswer<PpString>> {
        return client.requestGoals();
    }

    //sends message for renderGoals
    async updateGoals(client: CoqLspClient): Promise<void> {
        let goals: CoqGoalAnswer<PpString>;
        try {
            goals = await this.getGoals(client);
        } catch (error) {
            wpl.debug(`Failed to retrieve goals: ${error}`);
            this.failedGoals(error);
            return;
        }
        if (goals) {
            const visibility = WaterproofConfigHelper.get(WaterproofSetting.VisibilityOfHypotheses);
            this.postMessage({ type: MessageType.renderGoals, body: { goals, visibility } });
        }
    }

    //sends message for errorGoals
    failedGoals(e: unknown) {
        // FIXME: The error `e` should have a proper type instead of `unknown`.
        //        See `updateGoals` in extension.ts, where this `failedGoals`
        //        is called as the result of a Promise rejection.
        this.postMessage({ type: MessageType.errorGoals, body: e });
    }

    //deactivates panel
    disable() {
        this.deactivatePanel();
    }

}
