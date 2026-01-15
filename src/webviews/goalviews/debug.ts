import { Uri } from "vscode";
import { LspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";
import { RocqLspClient } from "../../lsp-client/rocq";

//the debug panel extends the GoalsBase class
export class DebugPanel extends GoalsBase {
    constructor(extensionUri: Uri, config: LspClientConfig) {
        super(extensionUri, config, "debug");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible) {
                // TODO: show previous goals?
            }
        });
    }

    //override updateGoals to activate the panel before posting the goals message
    override updateGoals(client: RocqLspClient): Promise<void> {
        this.activatePanel();
        return super.updateGoals(client);
    }
}
