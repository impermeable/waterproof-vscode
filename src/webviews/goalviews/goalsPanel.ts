import { Uri } from "vscode";
import { LspClientConfig } from "../../lsp-client/clientTypes";
import { WebviewEvents, WebviewState } from "../coqWebview";
import { GoalsBase } from "./goalsBase";

//the goals panel extends the GoalsBase class
export class GoalsPanel extends GoalsBase {

    // constructor to define the name and to listen for webview events
    constructor(extensionUri: Uri, config: LspClientConfig) {
        super(extensionUri, config, "goals");
        this.on(WebviewEvents.change, () => {
            if (this.state === WebviewState.visible) {
                // TODO: show last goals?
            }
        });
    }
}
