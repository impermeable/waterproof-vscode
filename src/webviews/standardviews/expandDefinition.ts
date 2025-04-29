import {
    Uri,
} from "vscode";
import { CoqWebview, WebviewEvents, WebviewState } from "../coqWebview";
import { MessageType } from "../../../shared";
import { IExecutor } from "../../components";

export class ExpandDefinition extends CoqWebview implements IExecutor {
    // Initialize the data for the results
    private data: string[] = ['no results'];

    constructor(extensionUri: Uri) {
        // Initialize the expand definition panel with the extension Uri and the webview name
        super(extensionUri, "expandDefinition", true);
        this.readyPanel();
        // Set up an event listener for WebviewEvents.change event
        this.on(WebviewEvents.change, (_e) => {
            switch (this.state) { // Check the state of the webview
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
                    // Get panel ready again
                    this.readyPanel()
                    break;
            }
        });
    }

    setResults(results: string[]): void {
        // Set the data property to the provided results
        this.data = results;
        // Send a postMessage to the webview with the MessageType.setData and the data
        this.postMessage({ type: MessageType.setData, body: this.data });
    }

}
