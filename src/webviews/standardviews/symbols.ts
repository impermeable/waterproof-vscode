import {
    Uri, 
} from "vscode";
import { CoqWebview, WebviewEvents, WebviewState } from "../coqWebview";

export class SymbolsPanel extends CoqWebview {
    constructor(extensionUri: Uri) {
        // Initialize the symbols panel with the extension Uri and the webview name
        super(extensionUri, "symbols");
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
                    this.readyPanel(); 
                    break; 
            }
        });
    }
}