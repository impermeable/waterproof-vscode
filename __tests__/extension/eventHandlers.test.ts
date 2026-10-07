// Unit tests for the WebviewManager event handlers on the Waterproof extension
// class (onEditorReady / onViewportHint / onFocus / onCursorChange / onCommand).
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// These handlers are plain prototype methods, so we exercise them in isolation
// by invoking them with a hand-rolled `this` context (`Waterproof.prototype.fn
// .call(fakeThis, ...)`) instead of constructing the full extension, which would
// pull in the entire VS Code activation path.

function helperMocks(): typeof import("../__helpers__/extension-mocks").extensionMocks {
  return require("../__helpers__/extension-mocks").extensionMocks; // eslint-disable-line @typescript-eslint/no-require-imports
}

jest.mock("vscode", () => helperMocks().vscode(), { virtual: true });
jest.mock("vscode-languageclient", () => helperMocks().languageClient(), {
  virtual: true,
});
jest.mock("../../src/lsp-client/commandExecutor", () =>
  helperMocks().commandExecutor(),
);
jest.mock("../../src/helpers", () => helperMocks().helpers());
jest.mock("../../src/pm-editor", () => helperMocks().pmEditor());
jest.mock("../../src/util", () => helperMocks().util());
jest.mock("../../src/components/enableButton", () =>
  helperMocks().enableButton(),
);
jest.mock("../../src/webviews/sidePanel", () => helperMocks().sidePanel());
jest.mock("../../src/webviews/standardviews/search", () =>
  helperMocks().search(),
);
jest.mock("../../src/webviews/standardviews/execute", () =>
  helperMocks().execute(),
);
jest.mock("../../src/webviews/standardviews/symbols", () =>
  helperMocks().symbols(),
);
jest.mock("../../src/webviews/standardviews/tactics", () =>
  helperMocks().tactics(),
);
jest.mock("../../src/webviews/goalviews/debug", () =>
  helperMocks().debugPanel(),
);
jest.mock("../../src/webviews/goalviews/goalsPanel", () =>
  helperMocks().goalsPanel(),
);
jest.mock("../../src/webviews/goalviews/compositeGoalsPanel", () =>
  helperMocks().compositeGoalsPanel(),
);
jest.mock("../../src/lsp-client/composite", () => helperMocks().composite());
jest.mock("../../src/lsp-client/rocq", () => helperMocks().rocq());
jest.mock("../../src/lsp-client/lean", () => helperMocks().lean());
jest.mock("../../src/helpers/exerciseSheet", () =>
  helperMocks().exerciseSheet(),
);

import { Position } from "vscode";
import { Waterproof } from "../../src/extension";
import { executeCommand } from "../../src/lsp-client/commandExecutor";
import { doc } from "../__helpers__/extension-mocks";

const executeCommandMock = executeCommand as jest.Mock;

type FakeDoc = ReturnType<typeof doc>;

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
