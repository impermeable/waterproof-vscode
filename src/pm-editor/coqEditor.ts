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
        }).catch((reason) => {
            console.error(`==> Failed to create editor view. \n==> The reason should be printed below.`);
            console.log(reason);
        });
    }

}
