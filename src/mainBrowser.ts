import { ExtensionContext, Uri, WorkspaceConfiguration } from "vscode";
import { LanguageClientProviderFactory } from "./lsp-client/clientTypes";
import {
  LanguageClient,
  LanguageClientOptions,
} from "vscode-languageclient/browser";
import { Waterproof } from "./extension";

/**
 * A `LanguageClient` that owns the web worker its server runs in.
 *
 * `vscode-languageclient/browser` only wraps the worker it is handed in a
 * message reader/writer; it never terminates it. Without this, restarting the
 * document checker would leave the previous wacoq worker running forever, each
 * one holding the filesystem it unzipped out of `core-fs.zip` and its own idle
 * loop.
 */
class WorkerLanguageClient extends LanguageClient {
  // Not named `worker`: the base class already declares a private field by
  // that name.
  private readonly lspWorker: Worker;

  constructor(
    worker: Worker,
    id: string,
    name: string,
    clientOptions: LanguageClientOptions,
  ) {
    super(id, name, clientOptions, worker);
    this.lspWorker = worker;
  }

  override async dispose(timeout?: number): Promise<void> {
    try {
      await super.dispose(timeout);
    } finally {
      this.lspWorker.terminate();
    }
  }
}

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
  // The worker is started by the provider rather than here, so that its
  // lifetime matches the client that terminates it. A provider that is never
  // called leaves no worker behind.
  return () => {
    const lspWorker = new Worker(
      Uri.joinPath(context.extensionUri, "out/wacoq_worker.js").toString(true),
    );
    lspWorker.postMessage(context.extensionUri.toString());
    return new WorkerLanguageClient(
      lspWorker,
      "waterproof",
      "Waterproof Document Checker",
      clientOptions,
    );
  };
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
