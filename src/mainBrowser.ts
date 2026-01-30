import { ExtensionContext, Uri, WorkspaceConfiguration } from "vscode";
import { LanguageClientProviderFactory } from "./lsp-client/clientTypes";
import { LanguageClient, LanguageClientOptions } from "vscode-languageclient/browser";
import { Waterproof } from "./extension";

/**
 * This function is responsible for creating Coq language client providers
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const getCoqClientProvider: LanguageClientProviderFactory = (
    context: ExtensionContext,
    clientOptions: LanguageClientOptions,
    _wsConfig: WorkspaceConfiguration
) => {
    const serverMain = Uri.joinPath(context.extensionUri, 'out/src/mainBrowser.js');
    // Start our own webworker
    new Worker(serverMain.toString(true));
    const lspWorker = new Worker(Uri.joinPath(context.extensionUri, 'out/wacoq_worker.js').toString(true));
    lspWorker.postMessage(context.extensionUri.toString());
    return () => new LanguageClient(
        "waterproof",
        "Waterproof Document Checker",
        clientOptions,
        lspWorker
    );
};

/**
 * This function is responsible for creating Lean language client providers
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const getLeanClientProvider: LanguageClientProviderFactory = (
    _context: ExtensionContext,
    _clientOptions: LanguageClientOptions,
    _wsConfig: WorkspaceConfiguration
) => {
    throw new Error("Not implemented");
};

export function activate(context: ExtensionContext): void {
    console.log("Browser activate function");
    const extension: Waterproof = new Waterproof(context, getCoqClientProvider, getLeanClientProvider, true);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
