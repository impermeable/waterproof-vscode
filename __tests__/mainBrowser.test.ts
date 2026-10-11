// Unit tests for the web entry point's Rocq client provider.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// `vscode-languageclient/browser` only wraps the worker it is handed in a
// message reader/writer; it never terminates it. `WorkerLanguageClient` closes
// that gap so restarting the document checker does not leave the previous wacoq
// worker running. What is covered here:
//   - the worker being started per client rather than per factory call,
//   - the worker being terminated when the client is disposed, including when
//     the LSP shutdown itself fails,
//   - the entry point declaring Rocq as the only language it supports.
//
// `WorkerLanguageClient` is module-private, so the tests reach it the way the
// extension does: through the `LanguageSupport` that `activate` hands over.

function helperMocks(): typeof import("./__helpers__/browser-client-mocks").browserMocks {
  return require("./__helpers__/browser-client-mocks").browserMocks; // eslint-disable-line @typescript-eslint/no-require-imports
}

jest.mock("vscode", () => helperMocks().vscodeModule(), { virtual: true });
jest.mock(
  "vscode-languageclient/browser",
  () => helperMocks().languageClientModule(),
  { virtual: true },
);
jest.mock("../src/extension", () => helperMocks().extensionModule());

import { activate } from "../src/mainBrowser";
import {
  baseDispose,
  FakeWorker,
  resetBrowserMocks,
  waterproofInstances,
} from "./__helpers__/browser-client-mocks";
import type { ExtensionContext, WorkspaceConfiguration } from "vscode";
import type { LanguageClientOptions } from "vscode-languageclient";
import type { LanguageClientProvider } from "../src/lsp-client/clientTypes";

const EXTENSION_URI = "file:///ext";
const WACOQ_URL = `${EXTENSION_URI}/out/wacoq_worker.js`;

function makeContext(): ExtensionContext {
  return {
    extensionUri: { toString: () => EXTENSION_URI },
    subscriptions: [],
  } as unknown as ExtensionContext;
}

/** Run `activate` and return the Rocq provider it registered. */
function activateAndGetProvider(): LanguageClientProvider {
  const context = makeContext();
  activate(context);
  const { languageSupport } = waterproofInstances[0];
  return languageSupport.rocq(
    context,
    {} as LanguageClientOptions,
    {} as WorkspaceConfiguration,
  );
}

beforeEach(() => {
  jest.clearAllMocks();
  resetBrowserMocks();
  (globalThis as { Worker?: unknown }).Worker = FakeWorker;
  // `activate` announces itself on the console; keep the test output readable.
  jest.spyOn(console, "log").mockImplementation(() => {});
});

afterEach(() => {
  delete (globalThis as { Worker?: unknown }).Worker;
  jest.restoreAllMocks();
});

describe("web entry point language support", () => {
  it("declares Rocq as the only supported language", () => {
    activate(makeContext());

    const { languageSupport, isWeb } = waterproofInstances[0];
    expect(languageSupport.rocq).toBeDefined();
    expect(languageSupport.lean).toBeUndefined();
    expect(isWeb).toBe(true);
  });
});

describe("Rocq client provider worker lifetime", () => {
  it("starts no worker until a client is actually built", () => {
    // The factory used to spawn the worker itself, so a provider that was never
    // called still booted a server.
    activateAndGetProvider();

    expect(FakeWorker.created).toHaveLength(0);
  });

  it("starts the wacoq worker and hands it the extension uri", () => {
    const provider = activateAndGetProvider();

    provider();

    expect(FakeWorker.created).toHaveLength(1);
    expect(FakeWorker.created[0].url).toBe(WACOQ_URL);
    expect(FakeWorker.created[0].postMessage).toHaveBeenCalledWith(
      EXTENSION_URI,
    );
  });

  it("gives every client its own worker", () => {
    const provider = activateAndGetProvider();

    provider();
    provider();

    expect(FakeWorker.created).toHaveLength(2);
    expect(FakeWorker.created[0]).not.toBe(FakeWorker.created[1]);
  });
});

describe("WorkerLanguageClient.dispose", () => {
  it("terminates the worker, after shutting the client down", async () => {
    const client = activateAndGetProvider()();
    const worker = FakeWorker.created[0];

    await client.dispose(1234);

    expect(baseDispose).toHaveBeenCalledWith(1234);
    expect(worker.terminate).toHaveBeenCalledTimes(1);
    // The worker must outlive the shutdown handshake, not the other way round.
    expect(baseDispose.mock.invocationCallOrder[0]).toBeLessThan(
      worker.terminate.mock.invocationCallOrder[0],
    );
  });

  it("terminates the worker even when the shutdown fails", async () => {
    // Otherwise a server that will not shut down cleanly leaks its worker,
    // which is exactly the case where the worker is most likely to be stuck.
    baseDispose.mockRejectedValue(new Error("shutdown timed out"));
    const client = activateAndGetProvider()();
    const worker = FakeWorker.created[0];

    await expect(client.dispose()).rejects.toThrow("shutdown timed out");

    expect(worker.terminate).toHaveBeenCalledTimes(1);
  });

  it("terminates only its own worker", async () => {
    const provider = activateAndGetProvider();
    const first = provider();
    provider();

    await first.dispose();

    expect(FakeWorker.created[0].terminate).toHaveBeenCalledTimes(1);
    expect(FakeWorker.created[1].terminate).not.toHaveBeenCalled();
  });
});
