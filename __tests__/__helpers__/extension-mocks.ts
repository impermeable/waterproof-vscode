// Shared module factories for tests around the `Waterproof` extension class.
//
// `src/extension.ts` pulls in the whole activation path, so tests mock the
// module graph away and exercise prototype methods with a hand-rolled `this`
// context. These factories keep that (long) preamble in one place.
//
// Call them through a local `require` inside the `jest.mock` factory, as jest
// hoists `jest.mock` above the imports.

import type { LanguageClientSetups } from "../../src/lsp-client/clientTypes";

/** The arguments every mocked `CompositeClient` was constructed with. */
export const createdComposites: {
  setups: LanguageClientSetups;
  context: unknown;
}[] = [];

export function resetExtensionMocks(): void {
  createdComposites.length = 0;
}

export const extensionMocks = {
  vscode: () => ({
    Position: class {
      constructor(
        public line: number,
        public character: number,
      ) {}
    },
    commands: {
      registerCommand: jest.fn(),
      registerTextEditorCommand: jest.fn(),
      executeCommand: jest.fn(),
    },
    window: {
      createOutputChannel: jest.fn((name: string) => ({
        name,
        appendLine: jest.fn(),
        dispose: jest.fn(),
      })),
    },
    workspace: {},
    ConfigurationTarget: { Global: 1 },
    Uri: { parse: jest.fn(), joinPath: jest.fn() },
    RevealOutputChannelOn: { Info: 1 },
  }),

  languageClient: () => ({ RevealOutputChannelOn: { Info: 1 } }),

  commandExecutor: () => ({
    executeCommand: jest.fn(),
    executeCommandFullOutput: jest.fn(),
  }),

  helpers: () => ({
    WaterproofLogger: { log: jest.fn(), debug: jest.fn(), show: jest.fn() },
    WaterproofConfigHelper: {
      get: jest.fn(),
      update: jest.fn(),
      configuration: {},
    },
    WaterproofFileUtil: {},
    WaterproofPackageJSON: {
      // `initializeClient` slices the leading ">=" off this.
      requiredCoqLspVersion: jest.fn(() => ">=0.2.4"),
      requiredCoqWaterproofVersion: jest.fn(() => ">=3.1.0"),
    },
    WaterproofSetting: { SkipLaunchChecks: "skipLaunchChecks" },
  }),

  pmEditor: () => ({ WaterproofEditorProvider: { register: jest.fn() } }),

  util: () => ({
    // `initializeClient` attaches a `.catch` to this, so it has to be thenable.
    checkConflictingExtensions: jest.fn(() => Promise.resolve()),
    excludeRocqFileTypes: jest.fn(),
    checkTrimmingWhitespace: jest.fn(),
  }),

  enableButton: () => ({ WaterproofStatusBar: class {} }),
  sidePanel: () => ({ addSidePanel: jest.fn(), SidePanelProvider: class {} }),
  search: () => ({ Search: class {} }),
  execute: () => ({ ExecutePanel: class {} }),
  symbols: () => ({ SymbolsPanel: class {} }),
  tactics: () => ({ TacticsPanel: class {} }),
  debugPanel: () => ({ DebugPanel: class {} }),
  goalsPanel: () => ({ GoalsPanel: class {} }),
  compositeGoalsPanel: () => ({ CompositeGoalsPanel: class {} }),
  exerciseSheet: () => ({ clearInputCells: jest.fn() }),

  rocq: () => ({ RocqLspServerConfig: { create: jest.fn() } }),
  lean: () => ({ LeanLspServerConfig: { create: jest.fn() } }),

  /**
   * `CompositeClient` recording what `initializeClient` built it from, with an
   * inert client surface so the rest of `initializeClient` can run.
   */
  composite: () => ({
    CompositeClient: class CompositeClient {
      public readonly startWithHandlers = jest.fn(
        async (): Promise<string[]> => [],
      );
      public readonly prelaunchChecks = jest.fn(
        async (): Promise<string[]> => [],
      );
      public readonly dispose = jest.fn(async (): Promise<void> => {});
      public readonly isRunning = jest.fn(() => false);

      constructor(setups: LanguageClientSetups, context: unknown) {
        createdComposites.push({ setups, context });
      }
    },
  }),
};

/** A document double identified only by its uri. */
export function doc(uri: string): { uri: { toString: () => string } } {
  return { uri: { toString: () => uri } };
}
