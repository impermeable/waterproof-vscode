// Unit tests for CompositeGoalsPanel.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// CompositeGoalsPanel is a thin orchestration layer that decides, based on the
// composite client's active client, whether the goals panel should show the
// (Rocq) "goals" view or the (Lean) "infoview", and forwards state to the
// matching backend. The logic worth covering here is:
//   - the routing between the Lean (infoview) and non-Lean (goals) paths,
//   - the `lastState` bookkeeping that avoids redundant view switches,
//   - lazy creation vs. reuse of the InfoProvider,
//   - error handling on the Lean path,
//   - the change-event listener installed in the constructor, and
//   - the trivial delegations (failedGoals / disable / dispose).
//
// Everything around it (the panel, the composite client, the InfoProvider and
// the LeanLspClient) is mocked so that we exercise only CompositeGoalsPanel's
// own decision logic.

jest.mock(
  "vscode",
  () => ({
    window: {
      createOutputChannel: jest.fn(() => ({
        appendLine: jest.fn(),
        dispose: jest.fn(),
        show: jest.fn(),
      })),
    },
    ViewColumn: { Beside: 2 },
  }),
  { virtual: true },
);

jest.mock("../../../src/helpers", () => ({
  WaterproofLogger: { debug: jest.fn(), log: jest.fn(), show: jest.fn() },
}));

// LeanLspClient is used with `instanceof`, so it has to be a real class. We only
// need identity, not behaviour.
jest.mock("../../../src/lsp-client/lean", () => ({
  LeanLspClient: class LeanLspClient {},
}));

// InfoProvider is constructed lazily inside CompositeGoalsPanel; the mock records
// every constructed instance so the tests can assert on the calls made to it.
jest.mock("../../../src/infoview", () => ({
  InfoProvider: jest.fn().mockImplementation(() => ({
    initInfoview: jest.fn(),
    sendPosition: jest.fn(),
    resetServerState: jest.fn(),
    dispose: jest.fn(),
  })),
}));

import { CompositeGoalsPanel } from "../../../src/webviews/goalviews/compositeGoalsPanel";
import {
  WebviewEvents,
  WebviewState,
} from "../../../src/webviews/waterproofPanel";
import { LeanLspClient } from "../../../src/lsp-client/lean";
import { InfoProvider } from "../../../src/infoview";
import type { GoalsPanel } from "../../../src/webviews/goalviews/goalsPanel";
import type { CompositeClient } from "../../../src/lsp-client/composite";

const InfoProviderMock = InfoProvider as unknown as jest.Mock;

type MockPanel = {
  isOpened: boolean;
  state: WebviewState;
  on: jest.Mock;
  showView: jest.Mock;
  updateGoals: jest.Mock;
  failedGoals: jest.Mock;
  disable: jest.Mock;
  dispose: jest.Mock;
  /** Fire the WebviewEvents.change listener registered by the constructor. */
  triggerChange: () => void;
};

function makePanel(overrides: Partial<MockPanel> = {}): MockPanel {
  let changeCb: (() => void) | undefined;
  const panel: MockPanel = {
    isOpened: true,
    state: WebviewState.visible,
    on: jest.fn((event: WebviewEvents, cb: () => void) => {
      if (event === WebviewEvents.change) changeCb = cb;
    }),
    showView: jest.fn(),
    updateGoals: jest.fn().mockResolvedValue(undefined),
    failedGoals: jest.fn(),
    disable: jest.fn(),
    dispose: jest.fn(),
    triggerChange: () => changeCb?.(),
    ...overrides,
  };
  return panel;
}

/** Construct the panel under test from a mock panel (the only cast we need). */
function mount(panel: MockPanel = makePanel()): CompositeGoalsPanel {
  return new CompositeGoalsPanel(panel as unknown as GoalsPanel);
}

/** Build a composite-client-like object whose active client is a Lean client. */
function makeLeanClient(
  opts: {
    uri?: string;
    cursor?: { line: number; character: number };
  } = {},
): CompositeClient {
  const { uri = "file:///proof.lean", cursor } = opts;
  return {
    activeClient: new (LeanLspClient as unknown as new () => object)(),
    activeCursorPosition: cursor,
    activeDocument: { uri: { toString: () => uri } },
  } as unknown as CompositeClient;
}

/** Build a composite-client-like object whose active client is *not* Lean (Rocq). */
function makeRocqClient(): CompositeClient {
  const activeClient = { kind: "rocq" };
  return {
    activeClient,
    activeCursorPosition: undefined,
    activeDocument: undefined,
  } as unknown as CompositeClient;
}

/** Latest InfoProvider instance created by the code under test. */
function lastInfoProvider() {
  const results = InfoProviderMock.mock.results;
  return results[results.length - 1].value as {
    initInfoview: jest.Mock;
    sendPosition: jest.Mock;
    resetServerState: jest.Mock;
    dispose: jest.Mock;
  };
}

beforeEach(() => {
  jest.clearAllMocks();
});

describe("CompositeGoalsPanel constructor", () => {
  it("registers a change listener on the panel", () => {
    const panel = makePanel();
    mount(panel);
    expect(panel.on).toHaveBeenCalledWith(
      WebviewEvents.change,
      expect.any(Function),
    );
  });

  it("clears lastState when the panel reports a closed state", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    // Prime lastState by routing through the Lean path once.
    await comp.updateGoals(makeLeanClient());
    expect(panel.showView).toHaveBeenCalledWith("infoview");
    panel.showView.mockClear();

    // Panel closes: the listener should reset lastState so a later re-open
    // performs the view switch again.
    panel.state = WebviewState.closed;
    panel.triggerChange();

    panel.state = WebviewState.visible;
    await comp.updateGoals(makeLeanClient());
    expect(panel.showView).toHaveBeenCalledWith("infoview");
  });

  it("re-runs updateGoals with the last client when the panel becomes visible", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    // Establish a lastClient (Rocq is simplest as it delegates to updateGoals).
    const client = makeRocqClient();
    await comp.updateGoals(client);
    panel.updateGoals.mockClear();

    panel.state = WebviewState.visible;
    panel.triggerChange();
    // The change handler is synchronous but kicks off updateGoals; allow the
    // microtask to settle.
    await Promise.resolve();

    expect(panel.updateGoals).toHaveBeenCalledWith(client.activeClient);
  });

  it("does nothing on change when there is no last client", () => {
    const panel = makePanel();
    mount(panel);
    panel.state = WebviewState.visible;
    expect(() => panel.triggerChange()).not.toThrow();
    expect(panel.updateGoals).not.toHaveBeenCalled();
    expect(panel.showView).not.toHaveBeenCalled();
  });
});

describe("CompositeGoalsPanel.updateGoals guards", () => {
  it("returns early when the panel is not opened", async () => {
    const panel = makePanel({ isOpened: false });
    const comp = mount(panel);

    await comp.updateGoals(makeRocqClient());

    expect(panel.showView).not.toHaveBeenCalled();
    expect(panel.updateGoals).not.toHaveBeenCalled();
    expect(InfoProviderMock).not.toHaveBeenCalled();
  });
});

describe("CompositeGoalsPanel.updateGoals — Lean (infoview) path", () => {
  it("switches to the infoview and lazily creates an InfoProvider on the first call", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    await comp.updateGoals(
      makeLeanClient({
        uri: "file:///a.lean",
        cursor: { line: 3, character: 7 },
      }),
    );

    expect(panel.showView).toHaveBeenCalledWith("infoview");
    expect(InfoProviderMock).toHaveBeenCalledTimes(1);
    const provider = lastInfoProvider();
    expect(provider.initInfoview).toHaveBeenCalledTimes(1);
    expect(provider.sendPosition).not.toHaveBeenCalled();

    const loc = provider.initInfoview.mock.calls[0][0];
    expect(loc.uri).toBe("file:///a.lean");
    expect(loc.range.start).toEqual({ line: 3, character: 7 });
    expect(loc.range.end).toEqual({ line: 3, character: 7 });
  });

  it("defaults the location to 0:0 when there is no cursor position", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    await comp.updateGoals(makeLeanClient({ cursor: undefined }));

    const loc = lastInfoProvider().initInfoview.mock.calls[0][0];
    expect(loc.range.start).toEqual({ line: 0, character: 0 });
    expect(loc.range.end).toEqual({ line: 0, character: 0 });
  });

  it("reuses the existing InfoProvider and sends a position on subsequent Lean calls", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    await comp.updateGoals(
      makeLeanClient({ cursor: { line: 1, character: 1 } }),
    );
    const provider = lastInfoProvider();
    provider.initInfoview.mockClear();
    panel.showView.mockClear();

    await comp.updateGoals(
      makeLeanClient({ cursor: { line: 2, character: 4 } }),
    );

    // No second InfoProvider and no redundant view switch.
    expect(InfoProviderMock).toHaveBeenCalledTimes(1);
    expect(panel.showView).not.toHaveBeenCalled();
    expect(provider.initInfoview).not.toHaveBeenCalled();
    expect(provider.sendPosition).toHaveBeenCalledTimes(1);
    expect(provider.sendPosition.mock.calls[0][0].range.start).toEqual({
      line: 2,
      character: 4,
    });
  });

  it("resets the server state when re-entering the infoview after another state", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    // Lean -> creates provider (provider is undefined when reset is attempted,
    // so the first reset is a no-op).
    await comp.updateGoals(makeLeanClient());
    const provider = lastInfoProvider();
    expect(provider.resetServerState).not.toHaveBeenCalled();

    // Switch away to the goals view ...
    await comp.updateGoals(makeRocqClient());
    // ... then back to the infoview: now the existing provider is reset.
    await comp.updateGoals(makeLeanClient());

    expect(provider.resetServerState).toHaveBeenCalledTimes(1);
  });

  it("falls back to the goals view when initInfoview throws", async () => {
    const panel = makePanel();
    InfoProviderMock.mockImplementationOnce(() => ({
      initInfoview: jest.fn(() => {
        throw new Error("boom");
      }),
      sendPosition: jest.fn(),
      resetServerState: jest.fn(),
      dispose: jest.fn(),
    }));
    const comp = mount(panel);

    await comp.updateGoals(makeLeanClient());

    expect(panel.showView).toHaveBeenLastCalledWith("goals");
    expect(panel.failedGoals).toHaveBeenCalledTimes(1);
    expect(panel.failedGoals.mock.calls[0][0]).toBeInstanceOf(Error);
  });

  it("falls back to the goals view when sendPosition throws", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    await comp.updateGoals(makeLeanClient());
    const provider = lastInfoProvider();
    provider.sendPosition.mockImplementationOnce(() => {
      throw new Error("kaboom");
    });

    await comp.updateGoals(makeLeanClient());

    expect(panel.showView).toHaveBeenLastCalledWith("goals");
    expect(panel.failedGoals).toHaveBeenCalledTimes(1);
  });
});

describe("CompositeGoalsPanel.updateGoals — non-Lean (goals) path", () => {
  it("switches to the goals view and delegates to panel.updateGoals", async () => {
    const panel = makePanel();
    const comp = mount(panel);
    const client = makeRocqClient();

    await comp.updateGoals(client);

    expect(panel.showView).toHaveBeenCalledWith("goals");
    expect(panel.updateGoals).toHaveBeenCalledWith(client.activeClient);
    expect(InfoProviderMock).not.toHaveBeenCalled();
  });

  it("does not switch the view again on consecutive goals calls", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    await comp.updateGoals(makeRocqClient());
    panel.showView.mockClear();
    panel.updateGoals.mockClear();

    await comp.updateGoals(makeRocqClient());

    // The view is not switched again, but goals are still forwarded each time.
    expect(panel.showView).not.toHaveBeenCalled();
    expect(panel.updateGoals).toHaveBeenCalledTimes(1);
  });

  it("returns the promise from panel.updateGoals", async () => {
    const sentinel = Symbol("done");
    const panel = makePanel({
      updateGoals: jest.fn().mockResolvedValue(sentinel),
    });
    const comp = mount(panel);

    await expect(comp.updateGoals(makeRocqClient())).resolves.toBe(sentinel);
  });
});

describe("CompositeGoalsPanel delegations", () => {
  it("forwards failedGoals to the panel", () => {
    const panel = makePanel();
    const comp = mount(panel);
    const err = new Error("nope");

    comp.failedGoals(err);

    expect(panel.failedGoals).toHaveBeenCalledWith(err);
  });

  it("forwards disable to the panel", () => {
    const panel = makePanel();
    const comp = mount(panel);

    comp.disable();

    expect(panel.disable).toHaveBeenCalledTimes(1);
  });

  it("disposes the panel and the InfoProvider", async () => {
    const panel = makePanel();
    const comp = mount(panel);

    // Create an InfoProvider first so dispose has something to clean up.
    await comp.updateGoals(makeLeanClient());
    const provider = lastInfoProvider();

    comp.dispose();

    expect(panel.dispose).toHaveBeenCalledTimes(1);
    expect(provider.dispose).toHaveBeenCalledTimes(1);
  });

  it("disposes the panel even when no InfoProvider was created", () => {
    const panel = makePanel();
    const comp = mount(panel);

    expect(() => comp.dispose()).not.toThrow();
    expect(panel.dispose).toHaveBeenCalledTimes(1);
  });
});
