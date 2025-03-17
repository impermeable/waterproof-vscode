import { ExtensionContext, Uri, WorkspaceConfiguration } from "vscode";
import { CoqLspClientFactory } from "./lsp-client/clientTypes";
import { LanguageClient, LanguageClientOptions } from "vscode-languageclient/browser";
import { CoqLspClient } from "./lsp-client/client";
import { Waterproof } from "./extension";

/**
 * This function is responsible for creating lsp clients with the extended
 * functionality specified in the interface CoqFeatures
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const clientFactory: CoqLspClientFactory = (context: ExtensionContext, clientOptions: LanguageClientOptions, wsConfig: WorkspaceConfiguration) => {
    const serverMain = Uri.joinPath(context.extensionUri, 'out/src/mainBrowser.js');
	const worker = new Worker(serverMain.toString(true));
    const lspWorker = new Worker(Uri.joinPath(context.extensionUri, 'out/coq_lsp_worker.bc.js').toString(true));
    return new (CoqLspClient(LanguageClient))(
        "waterproof",
        "Waterproof Document Checker",
        clientOptions,
        lspWorker
    );
};


export function activate(context: ExtensionContext): void {
    console.log("Browser activate function");
    let extension: Waterproof = new Waterproof(context, clientFactory, true);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
