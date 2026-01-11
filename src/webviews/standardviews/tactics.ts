import {
    Uri,
} from "vscode";
import { CoqWebview, WebviewEvents, WebviewState } from "../coqWebview";

// Import the JSON data containing the Coq tactics
import dataCoq from "../../../completions/tactics.json";
// Import the JSON data for Lean tactics
import dataLean from "../../../completions/tacticsLean.json";
import { CompositeClient } from "../../lsp-client/composite";
import { CoqLspClient } from "../../lsp-client/coq";
import { LeanLspClient } from "../../lsp-client/lean";

export class TacticsPanel extends CoqWebview {
    private lastClient?: CoqLspClient | LeanLspClient;

    constructor(extensionUri: Uri) {
        // Initialize the tactics panel with the extension Uri and the webview name
        super(extensionUri,"tactics");

        this.readyPanel();
        // Set up an event listener for WebviewEvents.change event
        this.on(WebviewEvents.change,(_e) => {
            switch(this.state) { // Check the state of the webview
                // If the webview is open
                case WebviewState.open:
                    break;
                // If the webview is ready
                case WebviewState.ready:
                    break;
                // If the webview is visible
                case WebviewState.visible:
                    break;
                // If the webview is closed
                case WebviewState.closed:
                    // Get panel ready
                    this.readyPanel()
                    break;
            }
        });
    }

    update(client: CompositeClient) {
        if (this.lastClient === client.activeClient)
            return;

        if (client.activeClient instanceof LeanLspClient)
            this.showView("tactics", dataLean);
        else
            this.showView("tactics", dataCoq);

        this.lastClient = client.activeClient;
    }
}
