import { ExtensionContext } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { Waterproof } from "./extension";
import { CoqLspClient } from "./lsp-client/coqClient";
import { LeanLspClient } from "./lsp-client/leanClient";
import { LspClientFactory } from "./lsp-client/clientTypes";
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
export const leanClientFactory: LspClientFactory<LeanLspClient> = (_context, clientOptions) => {
    const serverOptions: ServerOptions = {
        // TODO: get from config
        command: "lake",
        args: ["serve"],
    };

    return new LeanLspClient(new LanguageClient(
        "waterproof_lean4_client",
        "Waterproof Document Checker (Lean 4)",
        serverOptions,
        clientOptions,
    ));
};

export const coqClientFactory: LspClientFactory<CoqLspClient> = (_context, clientOptions) => {
    const serverOptions: ServerOptions = {
        command: WaterproofConfigHelper.get(WaterproofSetting.Path),
        args: WaterproofConfigHelper.get(WaterproofSetting.Args),
    };
    return new CoqLspClient(new LanguageClient(
        "waterproof_rocq_client",
        "Waterproof Document Checker (Rocq)",
        serverOptions,
        clientOptions,
    ));
};

export function activate(context: ExtensionContext): WaterproofAPI {

    const extension = new Waterproof(context, leanClientFactory, coqClientFactory, false);
    context.subscriptions.push(extension);

    // start the lsp clients (Clients how start on focus event)
    // extension.initializeClient();    // Rocq client
    // extension.initializeLeanClient();   // Lean client

    // Expose the Waterproof API
    return {
        goals: extension.goals.bind(extension),
        currentDocument: extension.currentDocument.bind(extension),
        help: extension.help.bind(extension),
        proofContext: extension.proofContext.bind(extension),
        tryProof: extension.tryProof.bind(extension),
    }
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
