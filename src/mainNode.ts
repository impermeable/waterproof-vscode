import { ExtensionContext } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { Waterproof } from "./extension";
import { CoqLspClient } from "./lsp-client/client";
import { CoqLspClientFactory } from "./lsp-client/clientTypes";
import { WaterproofConfigHelper, WaterproofSetting } from "./helpers";
import { WaterproofAPI } from "./api";

/**
 * This function is responsible for creating lsp clients with the extended
 * functionality specified in the interface CoqFeatures
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const clientFactory: CoqLspClientFactory = (context : ExtensionContext, clientOptions: LanguageClientOptions) => {
    const serverOptions: ServerOptions = {
        command: WaterproofConfigHelper.get(WaterproofSetting.Path),
        args: WaterproofConfigHelper.get(WaterproofSetting.Args),
    };
    return new (CoqLspClient(LanguageClient))(
        "waterproof",
        "Waterproof Document Checker",
        serverOptions,
        clientOptions,
    );
};

export function activate(context: ExtensionContext): WaterproofAPI {
 
    const extension = new Waterproof(context, clientFactory, false);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();

    // Expose the Waterproof API
    return {
        goals: extension.goals.bind(extension),
        currentDocument: extension.currentDocument.bind(extension),
        help: extension.help.bind(extension),
        execCommand: extension.execCommand.bind(extension),
        proofContext: extension.proofContext.bind(extension),
        tryProof: extension.tryProof.bind(extension),
        cursorPosition: extension.cursorPosition.bind(extension),
    }
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
