// Shared doubles for tests around `CompositeClient`.
//
// `CompositeClient` constructs a `RocqLspClient` and (when configured) a
// `LeanLspClient`. Both are replaced by `FakeLspClient` subclasses so the tests
// exercise only the composite's own routing and lifecycle logic.

import type {
  LanguageClientSetup,
  LanguageClientSetups,
} from "../../src/lsp-client/clientTypes";

/**
 * Stand-in for an `LspClient`, exposing the surface `CompositeClient` touches.
 *
 * Defaults are deliberately inert (nothing running, no languages allowed) so a
 * test only has to set up the parts it cares about.
 */
export class FakeLspClient {
  public language = "";
  /** Mirrors `LspClient.hasClient`: a client was created, running or not. */
  public hasClient = false;
  public activeDocument: unknown = undefined;
  public activeCursorPosition: unknown = undefined;

  public readonly isRunning = jest.fn<boolean, []>(() => false);
  public readonly prelaunchChecks = jest.fn(async (): Promise<string[]> => []);
  public readonly startWithHandlers = jest.fn(
    async (): Promise<string[]> => [],
  );
  public readonly dispose = jest.fn(async (): Promise<void> => {});
  public readonly requestSymbols = jest.fn(async () => []);
  public readonly updateCompletions = jest.fn(async () => {});
  public readonly sendViewportHint = jest.fn();
  public readonly requestGoals = jest.fn();

  /** The arguments `CompositeClient` constructed this client with. */
  constructor(public readonly ctorArgs: unknown[]) {}
}

/** Every fake client constructed since the last {@link resetCreatedClients}. */
export const createdClients: { rocq: FakeLspClient[]; lean: FakeLspClient[] } =
  {
    rocq: [],
    lean: [],
  };

export function resetCreatedClients(): void {
  createdClients.rocq.length = 0;
  createdClients.lean.length = 0;
}

/**
 * Module factories for `jest.mock`.
 *
 * Call these through a local `require` inside the mock factory, as jest hoists
 * `jest.mock` above the imports.
 */
export const compositeMocks = {
  rocqModule: () => ({
    RocqLspClient: class RocqLspClient extends FakeLspClient {
      constructor(...args: unknown[]) {
        super(args);
        this.language = "rocq";
        createdClients.rocq.push(this);
      }
    },
  }),
  leanModule: () => ({
    LeanLspClient: class LeanLspClient extends FakeLspClient {
      constructor(...args: unknown[]) {
        super(args);
        this.language = "lean4";
        createdClients.lean.push(this);
      }
    },
  }),
  helpers: () => ({
    WaterproofLogger: { log: jest.fn(), debug: jest.fn(), show: jest.fn() },
  }),
};

/** A `LanguageClientSetup` whose provider and channel factory are spies. */
export type SpySetup = LanguageClientSetup & {
  provider: jest.Mock;
  createOutputChannel: jest.Mock;
};

export function makeSetup(): SpySetup {
  return {
    provider: jest.fn(() => ({}) as never),
    createOutputChannel: jest.fn(
      () => ({ appendLine: jest.fn(), dispose: jest.fn() }) as never,
    ),
  };
}

/** Setups for a build that supports Rocq only (the web extension). */
export function rocqOnlySetups(): LanguageClientSetups & { rocq: SpySetup } {
  return { rocq: makeSetup() };
}

/** Setups for a build that supports both languages (the desktop extension). */
export function bothSetups(): LanguageClientSetups & {
  rocq: SpySetup;
  lean: SpySetup;
} {
  return { rocq: makeSetup(), lean: makeSetup() };
}
