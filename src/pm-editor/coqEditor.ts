import * as vscode from "vscode";

import { WebviewManager } from "../webviewManager";
import { ProseMirrorWebview } from "./pmWebview";

/**
 * Provider for cat scratch editors.
 *
 * Cat scratch editors are used for `.cscratch` files, which are just json files.
 * To get started, run this extension and open an empty `.cscratch` file in VS Code.
 *
 * This provider demonstrates:
 *
 * - Setting up the initial webview for a custom editor.
 * - Loading scripts and styles in a custom editor.
 * - Synchronizing changes between a text document and a custom editor.
 */
export class CoqEditorProvider implements vscode.CustomTextEditorProvider {

    /** The vscode extension context */
    private readonly _context: vscode.ExtensionContext;

    /** The editor type */
    private static readonly viewType = 'coqEditor.coqEditor';

    /** The webview manager of the extension */
    private readonly _manager: WebviewManager;

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
        return ProseMirrorWebview.createProseMirrorView(webviewPanel, this._context.extensionUri, document).then((pmView) => {
            this._manager.addProseMirrorWebview(pmView);
        }).catch(() => {
            console.error(" Failed to create pm view ");
        });
    }

}
