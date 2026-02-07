import * as vscode from "vscode";

import { WebviewManager } from "../webviewManager";
import { ProseMirrorWebview } from "./pmWebview";

export class CoqEditorProvider implements vscode.CustomTextEditorProvider {

    /** The vscode extension context */
    private readonly _context: vscode.ExtensionContext;

    /** The editor type */
    private static readonly viewType = 'waterproofTue.waterproofEditor';

    /** The webview manager of the extension */
    private readonly _manager: WebviewManager;

    registeredHistoryCommands: boolean = false;
    _undoCommand: vscode.Disposable | undefined = undefined;
    _redoCommand: vscode.Disposable | undefined = undefined;
    _lastRegistered: ProseMirrorWebview | undefined = undefined;

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


    public registerHistoryCommandListeners(wantsToRegister: ProseMirrorWebview, undoListener: () => void, redoListener: () => void) {
        if (!this.registeredHistoryCommands) {
            this._context.subscriptions.push(
                this._undoCommand = vscode.commands.registerCommand("undo", undoListener),
                this._redoCommand = vscode.commands.registerCommand("redo", redoListener)
            );
        } else {
            // Update commands
            this.disposeHistoryCommandListeners(undefined); // force dispose
            this._context.subscriptions.push(
                this._undoCommand = vscode.commands.registerCommand("undo", undoListener),
                this._redoCommand = vscode.commands.registerCommand("redo", redoListener)
            );
        }
        this.registeredHistoryCommands = true;
        this._lastRegistered = wantsToRegister;
    }

    /**
     * Dispose the history command listeners.
     * @param wantsToDispose The webview that wants to dispose the listeners. If undefined, we force dispose of the listeners.
     */
    public disposeHistoryCommandListeners(wantsToDispose?: ProseMirrorWebview) {
        if ((wantsToDispose === undefined) || (this._lastRegistered == wantsToDispose)) {
            // Improvement: We don't need to dispose of the command if we switch from Waterproof editor to 
            //              Waterproof editor. In that case updating the listeners suffices.
            this._undoCommand?.dispose();
            this._redoCommand?.dispose();

            this.registeredHistoryCommands = false;
        }
    }
}
