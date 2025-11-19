import { ExtensionContext } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { Waterproof } from "./extension";
import { CoqLspClient } from "./lsp-client/coqClient";
import { LeanLspClient } from "./lsp-client/leanlspclient";
import { CoqLspClientFactory } from "./lsp-client/clientTypes";
import { WaterproofConfigHelper, WaterproofSetting } from "./helpers";
import { activateLeanClient, deactivateLeanClient, restartLeanClient }
    from "./lsp-client/leanlspclient";

export type LspClientFactory =
    (context: ExtensionContext, clientOptions: LanguageClientOptions, kind: ClientKind) => any;


/**
 * This function is responsible for creating lsp clients with the extended
 * functionality specified in the interface CoqFeatures
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const clientFactory: LspClientFactory = (context, clientOptions, kind) => {
    if (kind === 'lean') {
        return new LeanLspClient(context, clientOptions);
    }
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


export function activate(context: ExtensionContext): void {
    const extension: Waterproof = new Waterproof(context, clientFactory);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();
    extension.initializeLeanClient();
  /*   activateLeanClient(context).catch((err) => {
        console.error("Failed to activate Lean LSP client:", err);
    });
*/} 

export function deactivate(): void {
    // TODO: stop client
    return;
}
