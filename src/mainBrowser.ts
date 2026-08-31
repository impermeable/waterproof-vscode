import { ExtensionContext, Uri, WorkspaceConfiguration } from "vscode";
import { LanguageClientProviderFactory } from "./lsp-client/clientTypes";
import {
  LanguageClient,
  LanguageClientOptions,
} from "vscode-languageclient/browser";
import { Waterproof } from "./extension";

/**
 * This function is responsible for creating Rocq language client providers
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns an LSP client with the added functionality of `RocqFeatures`
 */
const getRocqClientProvider: LanguageClientProviderFactory = (
  context: ExtensionContext,
  clientOptions: LanguageClientOptions,
  _wsConfig: WorkspaceConfiguration,
) => {
  const lspWorker = new Worker(
    Uri.joinPath(context.extensionUri, "out/wacoq_worker.js").toString(true),
  );
  lspWorker.postMessage(context.extensionUri.toString());
  return () =>
    new LanguageClient(
      "waterproof",
      "Waterproof Document Checker",
      clientOptions,
      lspWorker,
    );
};

/**
 * Lean is not supported in the web version: there is no way to spawn the Lake
 * process the Lean server needs. The extension gates on this and never asks for
 * a Lean client, so the returned provider only exists as a backstop; note that
 * it must not throw here, as the factory itself is called during activation.
 *
 * @param clientOptions the options available for a LanguageClient (see vscode api)
 * @param wsConfig the workspace configuration of Waterproof
 * @returns a provider that rejects any attempt to create a Lean client
 */
const getLeanClientProvider: LanguageClientProviderFactory = (
  _context: ExtensionContext,
  _clientOptions: LanguageClientOptions,
  _wsConfig: WorkspaceConfiguration,
) => {
  return () => {
    throw new Error("Lean is not supported in the web version of Waterproof");
  };
};

export function activate(context: ExtensionContext): void {
  console.log("Browser activate function");
  const extension: Waterproof = new Waterproof(
    context,
    getRocqClientProvider,
    getLeanClientProvider,
    true,
  );
  context.subscriptions.push(extension);
  // start the lsp client
  extension.initializeClient();
}

export function deactivate(): void {
  // TODO: stop client
  return;
}
