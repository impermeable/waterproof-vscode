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

export function activate(context: ExtensionContext): void {
  console.log("Browser activate function");
  // No `lean` entry: this build cannot spawn the Lake process a Lean server
  // needs, so it declares Rocq as the only language it supports.
  const extension: Waterproof = new Waterproof(
    context,
    { rocq: getRocqClientProvider },
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
