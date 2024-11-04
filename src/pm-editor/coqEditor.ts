import * as vscode from "vscode";

import { WebviewManager } from "../webviewManager";
import { ProseMirrorWebview } from "./pmWebview";

export class CoqEditorProvider implements vscode.CustomTextEditorProvider {

    /** The vscode extension context */
    private readonly _context: vscode.ExtensionContext;

    /** The editor type */
    private static readonly viewType = 'coqEditor.coqEditor';

    /** The webview manager of the extension */
    private readonly _manager: WebviewManager;

    registeredHistoryCommands: boolean = false;
    _undoListener: (() => void) | undefined = undefined;
    _redoListener: (() => void) | undefined = undefined;
    _undoCommand: vscode.Disposable | undefined = undefined;
    _redoCommand: vscode.Disposable | undefined = undefined;

    public static register(context: vscode.ExtensionContext, manager: WebviewManager): vscode.Disposable {
        const provider = new CoqEditorProvider(context, manager);
        const providerRegistration = vscode.window.registerCustomEditorProvider(CoqEditorProvider.viewType, provider, {
            webviewOptions: {
                retainContextWhenHidden: false,
            }
        });
        return providerRegistration;
    }

    constructor(context: vscode.ExtensionContext, manager: WebviewManager) {
        this._context = context;
        this._manager = manager;
    }

    /**
     * Called when our custom editor is opened.
     */
    public async resolveCustomTextEditor(
        document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel,
        _token: vscode.CancellationToken
    ): Promise<void> {
        return ProseMirrorWebview.createProseMirrorView(webviewPanel, this._context.extensionUri, document, this).then((pmView) => {
            this._manager.addProseMirrorWebview(pmView);
        }).catch((reason) => {
            console.error(`==> Failed to create editor view. \n==> The reason should be printed below.`);
            console.log(reason);
        });
    }


    public registerHistoryCommandListeners(undoListener: () => void, redoListener: () => void) {
        this._undoListener = undoListener;
        this._redoListener = redoListener;

        if (!this.registeredHistoryCommands) {
            this._context.subscriptions.push(
                this._undoCommand = vscode.commands.registerCommand('undo', () => {
                    if (this._undoListener) {
                        this._undoListener();
                    }
                }),
                this._redoCommand = vscode.commands.registerCommand('redo', () => {
                    if (this._redoListener) {
                        this._redoListener();
                    }
                })
            );
            this.registeredHistoryCommands = true;
        }
    }

    public disposeHistoryCommandListeners() {
        // Improvement: We don't need to dispose of the command if we switch from Waterproof editor to 
        //              Waterproof editor. In that case updating the listeners suffices.
        this._undoCommand?.dispose();
        this._redoCommand?.dispose();

        this._undoListener = undefined;
        this._redoListener = undefined;
        this.registeredHistoryCommands = false;
    }
}
