import { EventEmitter } from "events";
import {
    Uri,
    ViewColumn,
    WebviewPanel,
    window
} from "vscode";
import { Disposable } from "vscode-languageclient";
import type { Message, TacticsData } from "../../shared";
import { WaterproofLogger as wpl } from "../helpers";
import { HypVisibility } from "../../lib/types";

/**
 * Defines the states of the webview
 */

export enum WebviewState {
    /** Closed and can't be made visible (i.e., any interaction is ignored). */
    closed = "closedWebview",
    /** Closed but can be made visible. */
    ready = "readyWebview",
    /** Open but not visible. For example, it's a hidden editor tab. */
    open = "openWebview",
    /** Open and visible. */
    visible = "visibleWebview",
    /** Open and primary selected. Only used for communication, never set as actual state. */
    focus = "focusWebview",
}

/**
 * Events emitted by Webview
 */
export enum WebviewEvents {
    change = "changedState",  // Webview change notification
    message = "receivedMessage",
    dispose = "disposedView",
    finishUpdate = "finishedUpdating", // Webviews in charge of doc changes
}

/**
 * This is the abstract webview class: it has four states.
 * It's only for UI webviews, not the editor.
 */
export abstract class CoqWebview extends EventEmitter implements Disposable {
    private _panel: WebviewPanel | null = null;
    private extensionUri: Uri;
    private _state: WebviewState;
    private name: string;
    /** Whether the webview contains an input field. */
    private readonly _supportInsert: boolean;
    private disposables: Disposable[] = [];

    constructor(extensionUri: Uri, name: string, supportInsert: boolean = false) {
        super();
        this.extensionUri = extensionUri;
        this.name = name;
        this._state = WebviewState.closed;
        this._supportInsert = supportInsert;
    }

    public get supportInsert() {
        return this._supportInsert;
    }

    public get isOpened() {
        return this._panel && (this._state == WebviewState.visible);
    }
    public get isHidden() {
        return (this._state == WebviewState.open);
    }

    public get state() {
        return this._state;
    }

    dispose() {
        this._panel?.dispose();
        for (const d of this.disposables) {
            d.dispose();
        }
    }

    protected create() {
        if (this.state != WebviewState.ready) return; // Error handling

        const webviewOpts = { enableScripts: true, enableFindWidget: false, retainContextWhenHidden: this.name == "goals" };
        if (this.name == "help") {
            this._panel = window.createWebviewPanel(
                this.name,
                "Help",
                { preserveFocus: true, viewColumn: ViewColumn.Two },
                webviewOpts
            );
        } else if (this.name == "search") {
            this._panel = window.createWebviewPanel(
                this.name,
                "Search",
                { preserveFocus: true, viewColumn: ViewColumn.Two },
                webviewOpts
            );
        } else {
            this._panel = window.createWebviewPanel(
                this.name,
                this.name.charAt(0).toUpperCase() + this.name.slice(1),
                { preserveFocus: true, viewColumn: ViewColumn.Two },
                webviewOpts,
            );
        }


        this._panel.onDidChangeViewState((e) => {
            if(e.webviewPanel.active) this.emit(WebviewEvents.change, WebviewState.focus);
            if(e.webviewPanel.visible) {
                this.changeState(WebviewState.visible);
            } else {
                this.changeState(WebviewState.open);
            }
        });

        this._panel.webview.onDidReceiveMessage((msg) => {
            this.emit(WebviewEvents.message, msg);
        });

        this.showView(this.name);

        this.disposables.push(this._panel.onDidDispose(() => {
            // Once the panel has been disposed (for example when the user has closed the panel), we close (in terms of state) it here.
            this.closePanel();
        }));
    }

    /**
     * Set the webview's content to the view with the given name,
     * optionally passing `data` into window.extraData.
     */
    showView(name: string, data?: TacticsData) {
        if (!this._panel) {
            wpl.debug(`Could not show ${name}, WebviewPanel does not exist`);
            return;
        }

        const styleUri = this._panel.webview.asWebviewUri(
            Uri.joinPath(this.extensionUri, "out", "views", name, "index.css")
        );

        const scriptUri = this._panel.webview.asWebviewUri(
            Uri.joinPath(this.extensionUri, "out", "views", name, "index.js")
        );

        // TODO: remove this workaround (inject/load necessary resources from views/infoview/index.ts)
        if (name === 'infoview') {
            const distBase = this._panel.webview.asWebviewUri(
                Uri.joinPath(this.extensionUri, "node_modules", "@leanprover", "infoview", "dist")
            );
            const libPostfix = `.production.min.js`
            
            this._panel.webview.html = `
                <!DOCTYPE html>
                <html>
                <head>
                    <meta charset="UTF-8" />
                    <meta http-equiv="Content-type" content="text/html;charset=utf-8">
                    <title>Infoview</title>
                    <link rel="stylesheet" href="${distBase}/index.css">
                </head>
                <body>
                    <div id="root"></div>
                    <script
                        data-importmap-leanprover-infoview="${distBase}/index${libPostfix}"
                        data-importmap-react="${distBase}/react${libPostfix}"
                        data-importmap-react-jsx-runtime="${distBase}/react-jsx-runtime${libPostfix}"
                        data-importmap-react-dom="${distBase}/react-dom${libPostfix}"
                        src="${scriptUri}"></script>
                </body>
                </html>
            `;
            return;
        }

        this._panel.webview.html = `
            <!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <link rel="stylesheet" type="text/css" href="${styleUri}">
                <script>`
                    /* Allow for passing custom parameters to views.
                       This is used to pass the language-specific
                       tactics data to the tactics panel.
                     */
                    + `
                    window.extraData = ${JSON.stringify(data)};
                </script>
                <script src="${scriptUri}" type="module"></script>
                <title>Coq's info panel</title>
            </head>
            <body>
                <div id="root"></div>
            </body>
            </html>
        `;
    }

    /**
     * Closes the panel
     */
    private closePanel() {
        // Update the state to closed
        this.changeState(WebviewState.closed);
        // Remove the webview panel instance
        this._panel = null;
    }

    /**
     * Helper function to allow for proper state transitions
     *
     * @param next next webviewstate
     */
    private changeState(next: WebviewState) {
        if (next === this._state) return;
        const prev = this._state;
        this._state = next;
        this.emit(WebviewEvents.change, prev);

    }

    /**
     * Activate the panel if possible
     */
    public activatePanel() {
        if (this.state == WebviewState.ready) {
            this.create();
            this.changeState(WebviewState.open);
        }
    }

    /**
     * Reveal the panel if possible
     */
    public revealPanel() {
        if (!this._panel?.visible) {
            this._panel?.reveal(ViewColumn.Two);
        }
    }

    /**
     * Deactivate the panel
     */
    public deactivatePanel() {
        this._panel?.dispose();
        this.closePanel();
    }

    /**
     * Change the panel state to the ready state
     */
    public readyPanel() {
        if(this._state != WebviewState.closed) return;
        this.changeState(WebviewState.ready);
    }

    /**
     * Attempts to post a message to the webview, will result in a failure
     * if the webview is not visible
     *
     * @param type type of message (as in ./shared/Messages.ts)
     * @param params body of message
     * @returns boolean on whether message was sent successfully
     */
    public postMessage(msg: Message) : boolean {
        if (this.state != WebviewState.visible) {
            this.changeState(WebviewState.visible);
        }
        this._panel?.webview.postMessage(msg);
        return true;
    }

}
