// Unit tests for the WebviewManager event handlers on the Waterproof extension
// class (onEditorReady / onViewportHint / onFocus / onCursorChange / onCommand).
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// These handlers are plain prototype methods, so we exercise them in isolation
// by invoking them with a hand-rolled `this` context (`Waterproof.prototype.fn
// .call(fakeThis, ...)`) instead of constructing the full extension, which would
// pull in the entire VS Code activation path.

jest.mock(
  "vscode",
  () => ({
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
      createOutputChannel: jest.fn(() => ({
        appendLine: jest.fn(),
        dispose: jest.fn(),
      })),
    },
    workspace: {},
    ConfigurationTarget: { Global: 1 },
    Uri: { parse: jest.fn(), joinPath: jest.fn() },
    RevealOutputChannelOn: { Info: 1 },
  }),
  { virtual: true },
);

jest.mock(
  "vscode-languageclient",
  () => ({
    RevealOutputChannelOn: { Info: 1 },
  }),
  { virtual: true },
);

// The handlers only touch a couple of collaborators; everything else imported by
// extension.ts is mocked away so the module loads cheaply.
jest.mock("../../src/lsp-client/commandExecutor", () => ({
  executeCommand: jest.fn(),
  executeCommandFullOutput: jest.fn(),
}));
jest.mock("../../src/helpers", () => ({
  WaterproofLogger: { log: jest.fn(), debug: jest.fn(), show: jest.fn() },
  WaterproofConfigHelper: {
    get: jest.fn(),
    update: jest.fn(),
    configuration: {},
  },
  WaterproofFileUtil: {},
  WaterproofPackageJSON: {},
  WaterproofSetting: {},
}));

// The remaining imports of extension.ts are only used to build the live
// extension; for these tests we just need them to be loadable.
jest.mock("../../src/pm-editor", () => ({
  WaterproofEditorProvider: { register: jest.fn() },
}));
jest.mock("../../src/util", () => ({
  checkConflictingExtensions: jest.fn(),
  excludeRocqFileTypes: jest.fn(),
  checkTrimmingWhitespace: jest.fn(),
}));
jest.mock("../../src/components/enableButton", () => ({
  WaterproofStatusBar: class {},
}));
jest.mock("../../src/webviews/sidePanel", () => ({
  addSidePanel: jest.fn(),
  SidePanelProvider: class {},
}));
jest.mock("../../src/webviews/standardviews/search", () => ({
  Search: class {},
}));
jest.mock("../../src/webviews/standardviews/execute", () => ({
  ExecutePanel: class {},
}));
jest.mock("../../src/webviews/standardviews/symbols", () => ({
  SymbolsPanel: class {},
}));
jest.mock("../../src/webviews/standardviews/tactics", () => ({
  TacticsPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/debug", () => ({
  DebugPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/goalsPanel", () => ({
  GoalsPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/compositeGoalsPanel", () => ({
  CompositeGoalsPanel: class {},
}));
jest.mock("../../src/lsp-client/composite", () => ({
  CompositeClient: class {},
}));
jest.mock("../../src/lsp-client/rocq", () => ({
  RocqLspServerConfig: { create: jest.fn() },
}));
jest.mock("../../src/lsp-client/lean", () => ({
  LeanLspServerConfig: { create: jest.fn() },
}));
jest.mock("../../src/helpers/exerciseSheet", () => ({
  clearInputCells: jest.fn(),
}));

import { Position } from "vscode";
import { Waterproof } from "../../src/extension";
import { executeCommand } from "../../src/lsp-client/commandExecutor";

const executeCommandMock = executeCommand as jest.Mock;

type FakeDoc = { uri: { toString: () => string } };

function doc(uri: string): FakeDoc {
  return { uri: { toString: () => uri } };
}

// Minimal stand-in for the `this` context the handlers rely on.
function makeCtx(overrides: Record<string, unknown> = {}) {
  return {
    clientRunning: true,
    client: {
      updateCompletions: jest.fn(),
      sendViewportHint: jest.fn(),
      rocqClient: { id: "rocq" },
      activeDocument: undefined as FakeDoc | undefined,
      activeCursorPosition: undefined as unknown,
    },
    webviewManager: { open: jest.fn() },
    goalsComponents: [{ updateGoals: jest.fn() }, { updateGoals: jest.fn() }],
    tacticsPanel: { update: jest.fn() },
    // onCursorChange delegates to updateGoals; stub it so we can test the
    // handler in isolation.
    updateGoals: jest.fn(),
    ...overrides,
  };
}

// Convenience accessors to the (private at compile time) prototype methods.
const proto = Waterproof.prototype as unknown as {
  onEditorReady: (this: unknown, d: FakeDoc) => void;
  onViewportHint: (
    this: unknown,
    p: { document: FakeDoc; start: number; end: number },
  ) => void;
  onFocus: (this: unknown, d: FakeDoc) => Promise<void>;
  onCursorChange: (this: unknown, d: FakeDoc, p: unknown) => void;
  onCommand: (
    this: unknown,
    source: { setResults: jest.Mock },
    command: string,
  ) => void;
};

beforeEach(() => {
  jest.clearAllMocks();
});

describe("onEditorReady", () => {
  it("refreshes completions for the ready document", () => {
    const ctx = makeCtx();
    const d = doc("file:///a.v");

    proto.onEditorReady.call(ctx, d);

    expect(ctx.client.updateCompletions).toHaveBeenCalledWith(d);
  });
});

describe("onViewportHint", () => {
  it("forwards the visible range to the client", () => {
    const ctx = makeCtx();
    const d = doc("file:///a.v");

    proto.onViewportHint.call(ctx, { document: d, start: 5, end: 42 });

    expect(ctx.client.sendViewportHint).toHaveBeenCalledWith(d, 5, 42);
  });
});

describe("onFocus", () => {
  it("makes a newly focused document active and refreshes goals/tactics", async () => {
    const ctx = makeCtx({
      client: {
        activeDocument: doc("file:///old.v"),
        activeCursorPosition: new Position(1, 1),
        updateCompletions: jest.fn(),
        sendViewportHint: jest.fn(),
        rocqClient: {},
      },
    });
    const d = doc("file:///new.v");

    await proto.onFocus.call(ctx, d);

    expect(ctx.client.activeDocument).toBe(d);
    expect(ctx.client.activeCursorPosition).toBeUndefined();
    expect(ctx.webviewManager.open).toHaveBeenCalledWith("goals");
    for (const g of ctx.goalsComponents) {
      expect(g.updateGoals).toHaveBeenCalledWith(ctx.client);
    }
    expect(ctx.tacticsPanel.update).toHaveBeenCalledWith(ctx.client);
  });

  it("does not reset the active document when focusing the same document", async () => {
    const same = doc("file:///same.v");
    const cursor = new Position(3, 7);
    const ctx = makeCtx({
      client: {
        activeDocument: same,
        activeCursorPosition: cursor,
        updateCompletions: jest.fn(),
        sendViewportHint: jest.fn(),
        rocqClient: {},
      },
    });

    await proto.onFocus.call(ctx, doc("file:///same.v"));

    // Same URI -> the document/cursor block is skipped ...
    expect(ctx.client.activeCursorPosition).toBe(cursor);
    expect(ctx.webviewManager.open).not.toHaveBeenCalled();
    for (const g of ctx.goalsComponents) {
      expect(g.updateGoals).not.toHaveBeenCalled();
    }
    // ... but the tactics panel is always refreshed.
    expect(ctx.tacticsPanel.update).toHaveBeenCalledWith(ctx.client);
  });

  it("waits for the client to start before proceeding", async () => {
    jest.useFakeTimers();
    try {
      const ctx = makeCtx({ clientRunning: false });
      const d = doc("file:///a.v");

      const pending = proto.onFocus.call(ctx, d);
      let resolved = false;
      pending.then(() => {
        resolved = true;
      });

      // Still blocked while the client is down.
      await Promise.resolve();
      jest.advanceTimersByTime(100);
      await Promise.resolve();
      expect(resolved).toBe(false);
      expect(ctx.tacticsPanel.update).not.toHaveBeenCalled();

      // Client comes up -> the polling interval lets the handler continue.
      ctx.clientRunning = true;
      jest.advanceTimersByTime(100);
      await pending;

      expect(resolved).toBe(true);
      expect(ctx.tacticsPanel.update).toHaveBeenCalledWith(ctx.client);
    } finally {
      jest.useRealTimers();
    }
  });
});

describe("onCursorChange", () => {
  it("updates the active document/cursor and requests goals", () => {
    const ctx = makeCtx();
    const d = doc("file:///a.v");
    const pos = new Position(4, 2);

    proto.onCursorChange.call(ctx, d, pos);

    expect(ctx.client.activeDocument).toBe(d);
    expect(ctx.client.activeCursorPosition).toBe(pos);
    expect(ctx.updateGoals).toHaveBeenCalledWith(d, pos);
  });
});

describe("onCommand", () => {
  it("short-circuits the createHelp command without touching the client", () => {
    const ctx = makeCtx();
    const source = { setResults: jest.fn() };

    proto.onCommand.call(ctx, source, "createHelp");

    expect(source.setResults).toHaveBeenCalledWith(["createHelp"]);
    expect(executeCommandMock).not.toHaveBeenCalled();
  });

  it("runs an ordinary command and forwards its results", async () => {
    const ctx = makeCtx();
    const source = { setResults: jest.fn() };
    executeCommandMock.mockResolvedValue(["goal 1", "goal 2"]);

    proto.onCommand.call(ctx, source, "Check nat.");
    await Promise.resolve();
    await Promise.resolve();

    expect(executeCommandMock).toHaveBeenCalledWith(
      ctx.client.rocqClient,
      "Check nat.",
    );
    expect(source.setResults).toHaveBeenCalledWith(["goal 1", "goal 2"]);
  });

  it("reports an error result when the command rejects", async () => {
    const ctx = makeCtx();
    const source = { setResults: jest.fn() };
    executeCommandMock.mockRejectedValue(new Error("boom"));

    proto.onCommand.call(ctx, source, "Bad.");
    await Promise.resolve();
    await Promise.resolve();

    expect(source.setResults).toHaveBeenCalledWith(["Error: boom"]);
  });
});
