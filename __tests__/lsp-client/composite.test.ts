// Unit tests for CompositeClient's handling of an optional Lean client.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// A build that cannot run a Lean server (the web extension, which has no way to
// spawn a Lake process) supplies no `lean` entry in its `LanguageClientSetups`.
// The composite then has to behave as a Rocq-only client without any caller
// having to know about it. What is covered here:
//   - which clients (and output channels) the constructor creates,
//   - prelaunchChecks / isRunning / startWithHandlers with Lean absent,
//   - dispose guarding on `hasClient` rather than `isRunning`, so a client that
//     was created but failed to start is still released.
//
// `getClient`'s lean4-when-Lean-is-unsupported branch is deliberately left
// uncovered: that fallback is a known wart whose behaviour is not yet settled.

function helperMocks(): typeof import("../__helpers__/composite-mocks").compositeMocks {
  return require("../__helpers__/composite-mocks").compositeMocks; // eslint-disable-line @typescript-eslint/no-require-imports
}

jest.mock("vscode", () => ({}), { virtual: true });
jest.mock("../../src/lsp-client/rocq", () => helperMocks().rocqModule());
jest.mock("../../src/lsp-client/lean", () => helperMocks().leanModule());
jest.mock("../../src/helpers", () => helperMocks().helpers());
jest.mock("../../lib/types", () => ({ convertToString: jest.fn() }), {
  virtual: true,
});

import { CompositeClient } from "../../src/lsp-client/composite";
import {
  bothSetups,
  createdClients,
  resetCreatedClients,
  rocqOnlySetups,
  type FakeLspClient,
} from "../__helpers__/composite-mocks";
import type { ExtensionContext } from "vscode";
import type { WebviewManager } from "../../src/webviewManager";

const context = {} as ExtensionContext;
const webviewManager = {} as WebviewManager;

/** The Rocq double the composite constructed (typed for convenience). */
function rocqDouble(client: CompositeClient): FakeLspClient {
  return client.rocqClient as unknown as FakeLspClient;
}

/** The Lean double the composite constructed. Fails if there is none. */
function leanDouble(client: CompositeClient): FakeLspClient {
  if (!client.leanClient) throw new Error("expected a Lean client");
  return client.leanClient as unknown as FakeLspClient;
}

beforeEach(() => {
  jest.clearAllMocks();
  resetCreatedClients();
});

describe("CompositeClient construction", () => {
  it("creates no Lean client when the setups have no lean entry", () => {
    const setups = rocqOnlySetups();

    const client = new CompositeClient(setups, context);

    expect(client.rocqClient).toBeDefined();
    expect(client.leanClient).toBeUndefined();
    expect(createdClients.lean).toHaveLength(0);
    expect(createdClients.rocq).toHaveLength(1);
  });

  it("creates no Lean output channel when Lean is unsupported", () => {
    const setups = rocqOnlySetups();

    new CompositeClient(setups, context);

    // The Rocq channel is created eagerly; there is no Lean setup at all, so
    // nothing can create a channel for a server that can never start.
    expect(setups.rocq.createOutputChannel).toHaveBeenCalledTimes(1);
  });

  it("creates both clients, each with its own provider and channel", () => {
    const setups = bothSetups();
    const rocqChannel = { id: "rocq-channel" };
    const leanChannel = { id: "lean-channel" };
    setups.rocq.createOutputChannel.mockReturnValue(rocqChannel);
    setups.lean.createOutputChannel.mockReturnValue(leanChannel);

    const client = new CompositeClient(setups, context);

    expect(client.leanClient).toBeDefined();
    expect(setups.lean.createOutputChannel).toHaveBeenCalledTimes(1);
    // Each client gets its own language's provider and channel, in that order.
    expect(rocqDouble(client).ctorArgs).toEqual([
      setups.rocq.provider,
      rocqChannel,
      context,
    ]);
    expect(leanDouble(client).ctorArgs).toEqual([
      setups.lean.provider,
      leanChannel,
    ]);
  });

  it("does not invoke the providers itself", () => {
    // The provider is a thunk the client calls lazily; the composite only
    // hands it on. Calling it here would start a language server eagerly.
    const setups = bothSetups();

    new CompositeClient(setups, context);

    expect(setups.rocq.provider).not.toHaveBeenCalled();
    expect(setups.lean.provider).not.toHaveBeenCalled();
  });
});

describe("CompositeClient.prelaunchChecks", () => {
  it("returns only the Rocq languages when Lean is unsupported", async () => {
    const client = new CompositeClient(rocqOnlySetups(), context);
    rocqDouble(client).prelaunchChecks.mockResolvedValue(["rocq"]);

    await expect(client.prelaunchChecks()).resolves.toEqual(["rocq"]);
  });

  it("concatenates the languages of both clients", async () => {
    const client = new CompositeClient(bothSetups(), context);
    rocqDouble(client).prelaunchChecks.mockResolvedValue(["rocq"]);
    leanDouble(client).prelaunchChecks.mockResolvedValue(["lean4"]);

    await expect(client.prelaunchChecks()).resolves.toEqual(["rocq", "lean4"]);
  });
});

describe("CompositeClient.isRunning", () => {
  it("follows the Rocq client when Lean is unsupported", () => {
    const client = new CompositeClient(rocqOnlySetups(), context);

    expect(client.isRunning()).toBe(false);

    rocqDouble(client).isRunning.mockReturnValue(true);
    expect(client.isRunning()).toBe(true);
  });

  it("is true when either client runs", () => {
    const client = new CompositeClient(bothSetups(), context);

    expect(client.isRunning()).toBe(false);

    leanDouble(client).isRunning.mockReturnValue(true);
    expect(client.isRunning()).toBe(true);
  });
});

describe("CompositeClient.startWithHandlers", () => {
  it("starts only Rocq when Lean is unsupported", async () => {
    const client = new CompositeClient(rocqOnlySetups(), context);
    rocqDouble(client).startWithHandlers.mockResolvedValue(["rocq"]);

    const started = await client.startWithHandlers(webviewManager, [
      "rocq",
      "lean4",
    ]);

    // "lean4" being allowed must not resurrect a client that does not exist.
    expect(started).toEqual(["rocq"]);
    expect(rocqDouble(client).startWithHandlers).toHaveBeenCalledWith(
      webviewManager,
      ["rocq", "lean4"],
    );
  });

  it("starts both clients when both are supported and allowed", async () => {
    const client = new CompositeClient(bothSetups(), context);
    rocqDouble(client).startWithHandlers.mockResolvedValue(["rocq"]);
    leanDouble(client).startWithHandlers.mockResolvedValue(["lean4"]);

    const started = await client.startWithHandlers(webviewManager, [
      "rocq",
      "lean4",
    ]);

    expect(started).toEqual(["rocq", "lean4"]);
  });

  it("skips a supported client whose language is not allowed", async () => {
    const client = new CompositeClient(bothSetups(), context);
    rocqDouble(client).startWithHandlers.mockResolvedValue(["rocq"]);

    const started = await client.startWithHandlers(webviewManager, ["rocq"]);

    expect(started).toEqual(["rocq"]);
    expect(leanDouble(client).startWithHandlers).not.toHaveBeenCalled();
  });

  it("keeps the other client running when one fails to start", async () => {
    const client = new CompositeClient(bothSetups(), context);
    rocqDouble(client).startWithHandlers.mockResolvedValue(["rocq"]);
    leanDouble(client).startWithHandlers.mockRejectedValue(new Error("boom"));

    const started = await client.startWithHandlers(webviewManager, [
      "rocq",
      "lean4",
    ]);

    expect(started).toEqual(["rocq"]);
  });
});

describe("CompositeClient.dispose", () => {
  it("disposes a client that was created but never started", async () => {
    // Regression test: guarding on `isRunning` left a failed-start client
    // undisposed, orphaning the resources it owns (in the web build, the
    // worker its server runs in).
    const client = new CompositeClient(rocqOnlySetups(), context);
    const rocq = rocqDouble(client);
    rocq.hasClient = true;
    rocq.isRunning.mockReturnValue(false);

    await client.dispose(10);

    expect(rocq.dispose).toHaveBeenCalledWith(10);
  });

  it("does not dispose a client that was never created", async () => {
    // Reading `hasClient` must not be what brings a client into existence.
    const client = new CompositeClient(rocqOnlySetups(), context);
    const rocq = rocqDouble(client);
    rocq.hasClient = false;

    await client.dispose();

    expect(rocq.dispose).not.toHaveBeenCalled();
  });

  it("does not fail when Lean is unsupported", async () => {
    const client = new CompositeClient(rocqOnlySetups(), context);
    rocqDouble(client).hasClient = true;

    await expect(client.dispose()).resolves.toBeUndefined();
  });

  it("disposes both clients when both were created", async () => {
    const client = new CompositeClient(bothSetups(), context);
    rocqDouble(client).hasClient = true;
    leanDouble(client).hasClient = true;

    await client.dispose();

    expect(rocqDouble(client).dispose).toHaveBeenCalled();
    expect(leanDouble(client).dispose).toHaveBeenCalled();
  });
});
