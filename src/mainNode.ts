import { ExtensionContext, extensions, TextDocument } from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";
import { Waterproof } from "./extension";
import { CoqLspClient } from "./lsp-client/client";
import { CoqLspClientFactory } from "./lsp-client/clientTypes";
import { WaterproofConfigHelper, WaterproofSetting, WaterproofLogger as wpl } from "./helpers";

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

type WaterproofAPI = {
    requestGoals: () => Promise<{goal: string, hypotheses: string[]} | undefined>;
    currentDocument: () => TextDocument | undefined;
    helpOutput: () => Promise<string | undefined>;
    proofContext: () => { lemma: string, soFar: string, context: string} | undefined;
    tryProof: (steps: string) => Promise<{error?: string, finished: boolean, remainingGoals?: string[]}>; 
}

export function activate(context: ExtensionContext): WaterproofAPI {



    // We search for the Waterproof ProofBuddy extension
    const proofBuddyId = "waterproof-tue.waterproof-lemmi";
    const proofBuddyExtension = extensions.getExtension(proofBuddyId);
    
    const extension = new Waterproof(context, clientFactory, false);
    context.subscriptions.push(extension);
    // start the lsp client
    extension.initializeClient();

    if (proofBuddyExtension) {
        if (!proofBuddyExtension.isActive) {
            proofBuddyExtension.activate().then(() => {
                wpl.log("River extension activated.");
            });
        } else {
            wpl.log("River extension already active.");
        }
    }
    else {
        wpl.log("River extension not found... Continuing without it");
    }

    return {
        requestGoals: extension.currentGoals.bind(extension),
        currentDocument: extension.currentDocument.bind(extension),
        helpOutput: extension.helpOutput.bind(extension),
        proofContext: extension.proofContext.bind(extension),
        tryProof: extension.tryProof.bind(extension),
    }
}

export function deactivate(): void {
    // TODO: stop client
    return;
}
