// Doubles for the web entry point (`src/mainBrowser.ts`).
//
// The pieces it wires together — the browser `LanguageClient`, the `Worker` the
// wacoq server runs in, and the `Waterproof` class — are all replaced so the
// tests exercise only the entry point's own wiring.

import type { LanguageSupport } from "../../src/lsp-client/clientTypes";

/** Stands in for `BaseLanguageClient.dispose`, so tests can make it reject. */
export const baseDispose = jest.fn(
  async (_timeout?: number): Promise<void> => {},
);

/**
 * Stand-in for `vscode-languageclient/browser`'s `LanguageClient`.
 *
 * `dispose` has to live on the prototype (not be an instance field) for the
 * `super.dispose(...)` call in `WorkerLanguageClient` to reach it.
 */
export class FakeBrowserLanguageClient {
  constructor(
    public readonly id: string,
    public readonly name: string,
    public readonly clientOptions: unknown,
    public readonly worker: unknown,
  ) {}

  async dispose(timeout?: number): Promise<void> {
    await baseDispose(timeout);
  }
}

/** Stand-in for the DOM `Worker`, recording every instance created. */
export class FakeWorker {
  static readonly created: FakeWorker[] = [];

  public readonly postMessage = jest.fn();
  public readonly terminate = jest.fn();

  constructor(public readonly url: string) {
    FakeWorker.created.push(this);
  }
}

/** The arguments every `Waterproof` constructed by `activate` was given. */
export const waterproofInstances: {
  languageSupport: LanguageSupport;
  isWeb: boolean;
}[] = [];

export function resetBrowserMocks(): void {
  FakeWorker.created.length = 0;
  waterproofInstances.length = 0;
  baseDispose.mockClear();
  baseDispose.mockResolvedValue(undefined);
}

/**
 * Module factories for `jest.mock`.
 *
 * Call these through a local `require` inside the mock factory, as jest hoists
 * `jest.mock` above the imports.
 */
export const browserMocks = {
  vscodeModule: () => ({
    Uri: {
      joinPath: (base: { toString(): string }, ...parts: string[]) => ({
        toString: () => [base.toString(), ...parts].join("/"),
      }),
    },
  }),
  languageClientModule: () => ({ LanguageClient: FakeBrowserLanguageClient }),
  extensionModule: () => ({
    Waterproof: class Waterproof {
      public readonly initializeClient = jest.fn();
      constructor(
        _context: unknown,
        languageSupport: LanguageSupport,
        isWeb: boolean,
      ) {
        waterproofInstances.push({ languageSupport, isWeb });
      }
    },
  }),
};
