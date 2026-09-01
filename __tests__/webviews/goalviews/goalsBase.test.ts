// Unit tests for GoalsBase.updateGoals and the DebugPanel override.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// These panels render Rocq goals, but they are reached two different ways: the
// CompositeGoalsPanel hands them the Rocq client directly, while the goals
// components registered on the extension are handed the CompositeClient. The
// composite has no `requestGoals` of its own, so passing it straight through
// used to crash with "client.requestGoals is not a function" — swallowed by the
// try/catch and surfaced only as an empty panel. What is covered here:
//   - both client shapes resolving to the same Rocq client,
//   - the failure path posting errorGoals instead of renderGoals,
//   - DebugPanel activating its panel before delegating.
//
// DebugPanel is used as the concrete stand-in for the abstract GoalsBase, since
// it is also the class that actually receives a CompositeClient in production.

function panelMocks() {
  class WaterproofPanel {
    public readonly postMessage = jest.fn(() => true);
    public readonly activatePanel = jest.fn();
    public readonly deactivatePanel = jest.fn();
    public readonly on = jest.fn();
    constructor(
      public readonly extensionUri: unknown,
      public readonly name: string,
      public readonly supportInsert?: boolean,
    ) {}
  }
  return {
    WaterproofPanel,
    WebviewEvents: { change: "change" },
    WebviewState: { visible: "visible", closed: "closed" },
  };
}

jest.mock("vscode", () => ({}), { virtual: true });
jest.mock("../../../src/webviews/waterproofPanel", () => panelMocks());
jest.mock("../../../src/helpers", () => ({
  WaterproofLogger: { log: jest.fn(), debug: jest.fn(), show: jest.fn() },
  WaterproofConfigHelper: { get: jest.fn(() => "none") },
  WaterproofSetting: { VisibilityOfHypotheses: "visibilityOfHypotheses" },
}));

import { DebugPanel } from "../../../src/webviews/goalviews/debug";
// `MessageType` is a const enum, so its values are inlined at compile time and
// cannot be mocked; assert against the real ones.
import { MessageType } from "../../../shared";
import type { Uri } from "vscode";
import type { LspClientConfig } from "../../../src/lsp-client/clientTypes";
import type { CompositeClient } from "../../../src/lsp-client/composite";
import type { RocqLspClient } from "../../../src/lsp-client/rocq";

/** A Rocq client double that only answers goal requests. */
function makeRocqClient(): RocqLspClient & { requestGoals: jest.Mock } {
  return {
    requestGoals: jest.fn().mockResolvedValue({ goals: { goals: [] } }),
  } as unknown as RocqLspClient & { requestGoals: jest.Mock };
}

/**
 * A composite-client double. Deliberately has no `requestGoals` of its own, so
 * a panel that asked it directly would throw rather than silently pass.
 */
function makeComposite(rocqClient: RocqLspClient): CompositeClient {
  return { rocqClient } as unknown as CompositeClient;
}

function makePanel(): DebugPanel & {
  postMessage: jest.Mock;
  activatePanel: jest.Mock;
} {
  return new DebugPanel({} as Uri, {} as LspClientConfig) as DebugPanel & {
    postMessage: jest.Mock;
    activatePanel: jest.Mock;
  };
}

beforeEach(() => jest.clearAllMocks());

describe("GoalsBase.updateGoals client resolution", () => {
  it("requests goals from a Rocq client passed directly", async () => {
    const rocq = makeRocqClient();
    const panel = makePanel();

    await panel.updateGoals(rocq);

    expect(rocq.requestGoals).toHaveBeenCalledTimes(1);
    expect(panel.postMessage).toHaveBeenCalledWith(
      expect.objectContaining({ type: MessageType.renderGoals }),
    );
  });

  it("takes the Rocq client off a CompositeClient", async () => {
    // Regression test: the composite is what the extension's goals components
    // are handed, and it has no `requestGoals` of its own.
    const rocq = makeRocqClient();
    const composite = makeComposite(rocq);
    expect("requestGoals" in composite).toBe(false);
    const panel = makePanel();

    await panel.updateGoals(composite);

    expect(rocq.requestGoals).toHaveBeenCalledTimes(1);
    expect(panel.postMessage).toHaveBeenCalledWith(
      expect.objectContaining({ type: MessageType.renderGoals }),
    );
  });

  it("passes the configured hypothesis visibility along with the goals", async () => {
    const rocq = makeRocqClient();
    const goals = { goals: { goals: [{ ty: "nat" }] } };
    rocq.requestGoals.mockResolvedValue(goals);
    const panel = makePanel();

    await panel.updateGoals(makeComposite(rocq));

    expect(panel.postMessage).toHaveBeenCalledWith({
      type: MessageType.renderGoals,
      body: { goals, visibility: "none" },
    });
  });
});

describe("GoalsBase.updateGoals failure handling", () => {
  it("posts errorGoals and no goals when the request rejects", async () => {
    const rocq = makeRocqClient();
    const error = new Error("no active document");
    rocq.requestGoals.mockRejectedValue(error);
    const panel = makePanel();

    await panel.updateGoals(makeComposite(rocq));

    expect(panel.postMessage).toHaveBeenCalledWith({
      type: MessageType.errorGoals,
      body: error,
    });
    expect(panel.postMessage).not.toHaveBeenCalledWith(
      expect.objectContaining({ type: MessageType.renderGoals }),
    );
  });

  it("posts nothing when the request resolves without goals", async () => {
    const rocq = makeRocqClient();
    rocq.requestGoals.mockResolvedValue(undefined);
    const panel = makePanel();

    await panel.updateGoals(makeComposite(rocq));

    expect(panel.postMessage).not.toHaveBeenCalled();
  });
});

describe("DebugPanel.updateGoals", () => {
  it("activates the panel before delegating to GoalsBase", async () => {
    const rocq = makeRocqClient();
    const panel = makePanel();

    await panel.updateGoals(makeComposite(rocq));

    expect(panel.activatePanel).toHaveBeenCalledTimes(1);
    expect(rocq.requestGoals).toHaveBeenCalledTimes(1);
  });

  it("activates the panel even when the goal request fails", async () => {
    const rocq = makeRocqClient();
    rocq.requestGoals.mockRejectedValue(new Error("boom"));
    const panel = makePanel();

    await panel.updateGoals(makeComposite(rocq));

    expect(panel.activatePanel).toHaveBeenCalledTimes(1);
  });
});
