import { ExtensionContext, WorkspaceConfiguration } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { Coqnitive } from "./extension";
import { CoqLspClient } from "./lsp-client/client";
import { CoqLspClientFactory } from "./lsp-client/clientTypes";

/**
 * This function is responsible for creating lsp clients with the extended
 * functionality specified in the interface CoqFeatures
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of coqnitive
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const clientFactory: CoqLspClientFactory = (clientOptions: LanguageClientOptions, wsConfig: WorkspaceConfiguration) => {
    const serverOptions: ServerOptions = {
        command: wsConfig.path,
        args: wsConfig.args,
    };
    return new (CoqLspClient(LanguageClient))(
        "coqnitive",
        "Waterproof Document Checker",
        serverOptions,
        clientOptions,
    );
};


export function activate(context: ExtensionContext): void {
    let extension: Coqnitive = new Coqnitive(context, clientFactory);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
