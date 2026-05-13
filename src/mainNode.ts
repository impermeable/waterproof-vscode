import { ExtensionContext } from "vscode";
import { LanguageClient, LanguageClientOptions} from "vscode-languageclient/node";
import { Waterproof } from "./extension";
import { LanguageClientProvider, LanguageClientProviderFactory } from "./lsp-client/clientTypes";
import { WaterproofConfigHelper, WaterproofSetting } from "./helpers";
import { WaterproofAPI } from "./api";

/**
 * This function is responsible for creating Coq language client providers
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `CoqFeatures`
 */
const getCoqClientProvider: LanguageClientProviderFactory = (
    _context: ExtensionContext,
    clientOptions: LanguageClientOptions
): LanguageClientProvider => {
    return () => {
        const command = WaterproofConfigHelper.get(WaterproofSetting.Path)
        const args = WaterproofConfigHelper.get(WaterproofSetting.Args)
        return new LanguageClient(
        "waterproof",
        "Waterproof Document Checker",
        {
        command: command,
        args: args,
        },
        clientOptions,
    );
    }
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
    clientOptions: LanguageClientOptions
): LanguageClientProvider => {
    return () => {
        const command = WaterproofConfigHelper.get(WaterproofSetting.LakePath);
        const args = WaterproofConfigHelper.get(WaterproofSetting.LakeArgs).concat(["serve"]);
        return new LanguageClient(
        "waterproof",
        "Waterproof Document Checker",
        {
        command: command,
        args: args,
        },
        clientOptions,
    );
    }   
};

export function activate(context: ExtensionContext): WaterproofAPI {
    const extension = new Waterproof(context, getCoqClientProvider, getLeanClientProvider, false);
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
