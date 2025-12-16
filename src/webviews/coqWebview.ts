import { EventEmitter } from "events";
import {
    Uri,
    ViewColumn,
    WebviewPanel,
    window
} from "vscode";
import { Disposable } from "vscode-languageclient";
import { Message } from "../../shared";

export enum WebviewState {
    closed = "closedWebview",
    ready = "readyWebview",
    open = "openWebview",
    visible = "visibleWebview",
    focus = "focusWebview",
}

export enum WebviewEvents {
    change = "changedState",
    message = "receivedMessage",
    dispose = "disposedView",
    finishUpdate = "finishedUpdating",
}

export abstract class CoqWebview extends EventEmitter implements Disposable {
    // CHANGED: private -> protected
    protected _panel: WebviewPanel | null = null;
    protected extensionUri: Uri;
    protected _state: WebviewState;
    protected name: string;
    
    private readonly _supportInsert: boolean;
    protected disposables: Disposable[] = [];

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

    // CHANGED: protected visibility to allow override
    protected create() {
        if (this.state != WebviewState.ready) return;

        const webviewOpts = { enableScripts: true, enableFindWidget: false };
        // if (this.name == "help") {
        //     this._panel = window.createWebviewPanel(
        //         this.name,
        //         "Help",
        //         { preserveFocus: true, viewColumn: ViewColumn.Two },
        //         webviewOpts
        //     );
        // } else if (this.name == "search") {
        //     this._panel = window.createWebviewPanel(
        //         this.name,
        //         "Search",
        //         { preserveFocus: true, viewColumn: ViewColumn.Two },
        //         webviewOpts
        //     );
        // } else {
        this._panel = window.createWebviewPanel(
            this.name,
            this.name.charAt(0).toUpperCase() + this.name.slice(1),
            { preserveFocus: true, viewColumn: ViewColumn.Two },
            webviewOpts,
        );
        // }

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

        const styleUri = this._panel.webview.asWebviewUri(
            Uri.joinPath(this.extensionUri, "out", "views", this.name, "index.css")
        );

        const scriptUri = this._panel.webview.asWebviewUri(
            Uri.joinPath(this.extensionUri, "out", "views", this.name, "index.js")
        );

        if (this.name == "infoview") {
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
            </html>`
        } else {
            this._panel.webview.html = `
            <!DOCTYPE html>
            <html lang="en">
            <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <link rel="stylesheet" type="text/css" href="${styleUri}">
            <script src="${scriptUri}" type="module"></script>
            <title>Coq's info panel</title>
            </head>
            <body>
                <div id="root"></div>
            </body>
            </html>
            `;
        }

        this.disposables.push(this._panel.onDidDispose(() => {
            this.closePanel();
        }));
    }

    private closePanel() {
        this.changeState(WebviewState.closed);
        this._panel = null;
    }

    private changeState(next: WebviewState) {
        if (next === this._state) return;
        const prev = this._state;
        this._state = next;
        this.emit(WebviewEvents.change, prev);
    }

    public activatePanel() {
        if (this.state == WebviewState.ready) {
            this.create();
            this.changeState(WebviewState.open);
        }
    }

    public revealPanel() {
        if (!this._panel?.visible) {
            this._panel?.reveal(ViewColumn.Two);
        }
    }

    public deactivatePanel() {
        this._panel?.dispose();
        this.closePanel();
    }

    public readyPanel() {
        if (this._state != WebviewState.closed) return;
        this.changeState(WebviewState.ready);
    }

    public postMessage(msg: Message): boolean {
        // CHANGED: Guard against posting to a non-existent panel to avoid corrupting state
        if (!this._panel) {
            return false;
        }
        if (this.state != WebviewState.visible) {
            this.changeState(WebviewState.visible);
        }
        this._panel.webview.postMessage(msg);
        return true;
    }
}