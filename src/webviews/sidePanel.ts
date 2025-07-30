import * as vscode from 'vscode';
import { getNonce } from '../util';
import { WebviewManager, WebviewManagerEvents } from '../webviewManager';
// this function add the side panel to the vs code side panel
export function addSidePanel(context: vscode.ExtensionContext, manager: WebviewManager) {
    const provider = new SidePanelProvider(context.extensionUri, manager);
    context.subscriptions.push(
        vscode.window.registerWebviewViewProvider("sidePanel", provider));
    return provider;
}

export class SidePanelProvider implements vscode.WebviewViewProvider {
    public static readonly viewType = 'sidePanel';

    private _view?: vscode.WebviewView;
    private _transparencyMap: Map<string, boolean> = new Map();
    private readonly _greyedOutButtons: Set<string> = new Set();


    constructor(
        private readonly _extensionUri: vscode.Uri,
        private readonly _manager: WebviewManager,
    ) {
        this._manager.on(WebviewManagerEvents.buttonClick, (e) => {
            // Button flashes when clicked
            this.flashButton(e.name);
        });
    }


    private flashButton(buttonId: string) {
        // If the view is not available, return without flashing
        if (!this._view) return;
        // Post a message to the webview to flash the button
        this._view.webview.postMessage({
            type: 'flash',
            buttonId: buttonId,
        });
    }


    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        _context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this._view = webviewView;
       
        // Set options for the webview
        webviewView.webview.options = {
            enableScripts: true,
        };

        // Set the HTML content for the webview
        webviewView.webview.html = this._getHtmlForWebview(webviewView.webview);

        webviewView.webview.onDidReceiveMessage(message => {
            // Handle messages received from the webview
            if (message.command === 'executeScript') {
                // If the message is for executing a script, forward it to the webview
                webviewView.webview.postMessage({
                    command: 'executeScript',
                    script: message.script,
                });
            }
             else {
                // Handle other messages by opening the command in the manager
                this._manager.open(message.command);
            }
        });        
    }

    // Now we create the actual web page
    private _getHtmlForWebview(_webview: vscode.Webview) {
        const nonce = getNonce();

        // html code for the webview
        return `<!DOCTYPE html>
            <html lang="en">
            <head>
                <!-- CSS styles -->
                <style>
                .symbol-button {
                    background-color: var(--vscode-button-background);
                    color: var(--vscode-button-foreground);
                    border: none;
                    font-size: 12px;
                    cursor: pointer;
                    margin: 8px;
                    border-radius: 4px;
                    width: 100px;
                    height: 50px;
                    text-align: center;
                    vertical-align: top;
                }

                .symbol-button:hover {
                    background-color: var(--vscode-button-hoverBackground);
                }

                .flash {
                    animation: flashGrey 0.5s ease-in-out;
                }

                @keyframes flashGrey {
                    0% { opacity: 1; }
                    50% { opacity: 0.4; }
                    100% { opacity: 1; }
                }
            </style>
            </head>
            <body>
                <div class="symbol-container">
                    <button class="symbol-button" id="goals">Goals</button>
                    <button class="symbol-button" id="help">Help</button>
                    <button class="symbol-button" id="search">Search</button>
                    <button class="symbol-button" id="expandDefinition">Expand definition</button>
                    <button class="symbol-button" id="symbols">Symbols</button>
                    <button class="symbol-button" id="tactics">Tactics</button>
                    <button class="symbol-button" id="execute">Execute</button>
                    <button class="symbol-button" id="debug">Debug</button>
                </div>

                <script nonce="${nonce}">
                    const vscode = acquireVsCodeApi();

                    const goalsButton = document.getElementById('goals');
                    const debugButton = document.getElementById('debug');
                    const executeButton = document.getElementById('execute');
                    const helpButton = document.getElementById('help');
                    const searchButton = document.getElementById('search');
                    const expandButton = document.getElementById('expandDefinition');
                    const symbolsButton = document.getElementById('symbols');
                    const tacticsButton = document.getElementById('tactics');

                    goalsButton.addEventListener('click', () => {
                        // Handle Goals button click event by sending a message to vscode
                        vscode.postMessage({ command: 'goals' });
                    });

                    debugButton.addEventListener('click', () => {
                        // Handle debug button click event by sending a message to vscode
                        vscode.postMessage({ command: 'debug' });
                    });

                    executeButton.addEventListener('click', () => {
                        // Handle execute button click event by sending a message to vscode
                        vscode.postMessage({ command: 'execute' });
                    });

                    helpButton.addEventListener('click', () => {
                        // Handle commonExecute button click event by sending a message to vscode
                        vscode.postMessage({ command: 'help' });
                    });

                    searchButton.addEventListener('click', () => {
                        // Handle commonExecute button click event by sending a message to vscode
                        vscode.postMessage({ command: 'search' });
                    });

                    expandButton.addEventListener('click', () => {
                        // Handle expandDefinition button click event by sending a message to vscode
                        vscode.postMessage({ command: 'expandDefinition' });
                    });

                    symbolsButton.addEventListener('click', () => {
                        // Handle symbols button click event by sending a message to vscode
                        vscode.postMessage({ command: 'symbols' });
                    });

                    tacticsButton.addEventListener('click', () => {
                        // Handle tactics button click event by sending a message to vscode
                        vscode.postMessage({ command: 'tactics' });
                    });

                    //check for messages
                    window.addEventListener('message', event => {
                        const message = event.data;

                        if (message.type === 'flash') {
                            const button = document.getElementById(message.buttonId);
                            if (button) {
                                button.classList.add('flash');
                                setTimeout(() => {
                                    button.classList.remove('flash');
                                }, 500); 
                            }
                        }
                    });
                </script>
            </body>
        </html>`;
    }
}
