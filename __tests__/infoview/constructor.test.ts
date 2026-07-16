/* eslint-disable @typescript-eslint/no-explicit-any */
/**
 * Unit tests for the `InfoProvider` constructor in `src/infoview.ts`.
 *
 * The constructor is pure wiring: it builds an `Rpc` bound to the panel,
 * registers the editor API, subscribes to panel messages, configuration
 * changes and the client-stopped event, and records the resulting
 * disposables. These tests exercise that wiring by mocking `Rpc`, `vscode`
 * and the logger, and by driving fake `panel`/`client` objects.
 *
 * NOTE: a handful of tests below (grouped under "disposal") encode the
 * *intended* behaviour rather than the current behaviour, and are expected
 * to fail until the corresponding bugs are fixed. They are documented inline.
 */
import { EventEmitter } from "events";

// --- Module mocks -----------------------------------------------------------

// The real `Rpc` starts a 50ms `setInterval` on `register()` that repeatedly
// calls `panel.postMessage` and is never cleared by `InfoProvider.dispose()`.
// Mocking it keeps these tests deterministic and free of live timers, while
// still letting us assert the constructor's wiring. Each instance exposes its
// own `__api` so we can observe calls the provider makes through `getApi()`.
jest.mock("../../src/helpers/rpc", () => {
  const Rpc = jest.fn().mockImplementation(function (
    this: any,
    sendMessage: (m: any) => void,
  ) {
    this.sendMessage = sendMessage;
    this.register = jest.fn();
    this.messageReceived = jest.fn();
    this.__api = {
      initialize: jest.fn().mockResolvedValue(undefined),
      serverStopped: jest.fn().mockResolvedValue(undefined),
      serverRestarted: jest.fn().mockResolvedValue(undefined),
      changedCursorLocation: jest.fn().mockResolvedValue(undefined),
    };
    this.getApi = jest.fn(() => this.__api);
  });
  return { Rpc };
});

jest.mock("../../src/helpers/logger", () => ({
  WaterproofLogger: { log: jest.fn(), debug: jest.fn() },
}));

jest.mock(
  "vscode",
  () => ({
    workspace: {
      onDidChangeConfiguration: jest.fn(() => ({ dispose: jest.fn() })),
      getConfiguration: jest.fn(() => ({ get: jest.fn(), update: jest.fn() })),
    },
    ConfigurationTarget: { Global: 1 },
    env: { clipboard: { writeText: jest.fn() } },
    Position: class {
      constructor(
        public line: number,
        public character: number,
      ) {}
    },
    Disposable: class {},
  }),
  { virtual: true },
);

import { workspace } from "vscode";
import { Rpc } from "../../src/helpers/rpc";
import { InfoProvider } from "../../src/infoview";
import {
  qualifiedSettingName,
  WaterproofConfigHelper,
  WaterproofSetting,
} from "../../src/helpers";
import { WebviewEvents } from "../../src/webviews/waterproofPanel";
import { MessageType } from "../../shared";

// --- Test doubles -----------------------------------------------------------

/** Minimal stand-in for `GoalsPanel`: a real EventEmitter so `.on()` returns
 * `this` (matching Node semantics the constructor relies on), plus spies for
 * the two methods the provider calls. */
class FakePanel extends EventEmitter {
  postMessage = jest.fn();
  dispose = jest.fn();
}

/** Minimal stand-in for `LeanLspClient`, capturing the `clientStopped`
 * subscription so we can fire it and inspect the returned disposable. */
function makeFakeClient() {
  let stoppedCb: ((reason: any) => void) | undefined;
  const stoppedDisposable = { dispose: jest.fn() };
  return {
    stoppedDisposable,
    fireStopped: (reason: any) => stoppedCb?.(reason),
    clientStopped: jest.fn((cb: (reason: any) => void) => {
      stoppedCb = cb;
      return stoppedDisposable;
    }),
    // referenced by the (unused-here) editorApi closures
    client: {},
  };
}

/** Builds an `InfoProvider` over fresh test doubles and returns everything a
 * test might want to assert against. */
function makeProvider() {
  const panel = new FakePanel();
  const client = makeFakeClient();
  const provider = new InfoProvider(client as any, panel as any);
  const rpcInstance = (Rpc as jest.Mock).mock.instances[0] as any;
  return { panel, client, provider, rpc: rpcInstance };
}

/** The disposable returned by the last `onDidChangeConfiguration` call. */
function lastConfigDisposable() {
  const onChange = workspace.onDidChangeConfiguration as jest.Mock;
  return onChange.mock.results[onChange.mock.results.length - 1].value;
}

/** The handler passed to the last `onDidChangeConfiguration` call. */
function lastConfigHandler() {
  const onChange = workspace.onDidChangeConfiguration as jest.Mock;
  return onChange.mock.calls[onChange.mock.calls.length - 1][0] as (
    e: any,
  ) => void;
}

afterEach(() => {
  jest.clearAllMocks();
});

// --- Rpc wiring -------------------------------------------------------------

describe("InfoProvider constructor: Rpc wiring", () => {
  it("constructs a single Rpc whose send callback forwards to panel.postMessage", () => {
    const { panel, rpc } = makeProvider();

    expect(Rpc as jest.Mock).toHaveBeenCalledTimes(1);
    expect(typeof rpc.sendMessage).toBe("function");

    // The provider wires the Rpc's outgoing messages straight to the panel.
    const message = { kind: "initialize" };
    rpc.sendMessage(message);
    expect(panel.postMessage).toHaveBeenCalledWith(message);
  });

  it("registers the editor API with the Rpc and requests the api proxy", () => {
    const { rpc } = makeProvider();

    expect(rpc.register).toHaveBeenCalledTimes(1);
    // The registered object is the editor API surface used by the infoview.
    expect(rpc.register).toHaveBeenCalledWith(
      expect.objectContaining({
        saveConfig: expect.any(Function),
        sendClientRequest: expect.any(Function),
        createRpcSession: expect.any(Function),
        copyToClipboard: expect.any(Function),
      }),
    );
    expect(rpc.getApi).toHaveBeenCalledTimes(1);
  });
});

// --- Panel message routing --------------------------------------------------

describe("InfoProvider constructor: panel message subscription", () => {
  it("subscribes to WebviewEvents.message on the panel", () => {
    const { panel } = makeProvider();
    expect(panel.listenerCount(WebviewEvents.message)).toBe(1);
  });

  it("routes infoviewRpc messages into rpc.messageReceived (body only)", () => {
    const { panel, rpc } = makeProvider();
    const body = { seqNum: 7, name: "foo", args: [] };

    panel.emit(WebviewEvents.message, {
      type: MessageType.infoviewRpc,
      body,
    });

    expect(rpc.messageReceived).toHaveBeenCalledTimes(1);
    expect(rpc.messageReceived).toHaveBeenCalledWith(body);
  });

  it("ignores panel messages of other types", () => {
    const { panel, rpc } = makeProvider();

    panel.emit(WebviewEvents.message, {
      type: MessageType.setData,
      body: ["something"],
    });

    expect(rpc.messageReceived).not.toHaveBeenCalled();
  });
});

// --- Configuration-change subscription --------------------------------------

describe("InfoProvider constructor: configuration subscription", () => {
  it("subscribes to workspace configuration changes", () => {
    makeProvider();
    expect(workspace.onDidChangeConfiguration).toHaveBeenCalledTimes(1);
  });

  it("mirrors hypothesis visibility to the panel when that setting changes", () => {
    const { panel } = makeProvider();
    jest.spyOn(WaterproofConfigHelper, "get").mockReturnValue("none" as any);

    const affected = qualifiedSettingName(
      WaterproofSetting.VisibilityOfHypotheses,
    );
    lastConfigHandler()({
      affectsConfiguration: (name: string) => name === affected,
    });

    expect(panel.postMessage).toHaveBeenCalledWith({
      type: MessageType.setHypothesisVisibility,
      body: "none",
    });
  });

  it("does nothing when an unrelated setting changes", () => {
    const { panel } = makeProvider();
    jest.spyOn(WaterproofConfigHelper, "get").mockReturnValue("all" as any);

    lastConfigHandler()({
      affectsConfiguration: () => false,
    });

    expect(panel.postMessage).not.toHaveBeenCalled();
  });
});

// --- Client-stopped subscription --------------------------------------------

describe("InfoProvider constructor: client-stopped subscription", () => {
  it("subscribes to the client's clientStopped event", () => {
    const { client } = makeProvider();
    expect(client.clientStopped).toHaveBeenCalledTimes(1);
  });

  it("forwards a client stop to api.serverStopped with the reason", async () => {
    const { client, rpc } = makeProvider();
    const reason = { message: "boom" };

    client.fireStopped(reason);
    await Promise.resolve(); // let the fire-and-forget promise settle

    expect(rpc.__api.serverStopped).toHaveBeenCalledWith(reason);
  });
});

// --- Disposal ---------------------------------------------------------------

describe("InfoProvider constructor: disposal", () => {
  it("disposes the configuration subscription", () => {
    const { provider } = makeProvider();
    const configDisposable = lastConfigDisposable();

    provider.dispose();

    expect(configDisposable.dispose).toHaveBeenCalledTimes(1);
  });

  // ---- Intended-behaviour tests (expected to FAIL until the bugs are fixed) ----

  // BUG: `const sub = panel.on(...)` returns the panel itself (Node's
  // EventEmitter.on returns `this`), and `sub` is pushed into `disposables`.
  // So `dispose()` currently calls `panel.dispose()`, tearing down the whole
  // goals-panel webview. Disposing the InfoProvider should only detach its own
  // message listener, never dispose the panel.
  it("does NOT dispose the shared panel when the provider is disposed", () => {
    const { provider, panel } = makeProvider();

    provider.dispose();

    expect(panel.dispose).not.toHaveBeenCalled();
  });

  // BUG (same root cause): the message listener is never removed, so the
  // subscription leaks after disposal.
  it("removes its panel message listener on dispose", () => {
    const { provider, panel } = makeProvider();

    provider.dispose();

    expect(panel.listenerCount(WebviewEvents.message)).toBe(0);
  });

  // BUG: the Disposable returned by `client.clientStopped(...)` is discarded in
  // the constructor and never tracked, so the listener leaks past dispose().
  it("disposes the clientStopped subscription on dispose", () => {
    const { provider, client } = makeProvider();

    provider.dispose();

    expect(client.stoppedDisposable.dispose).toHaveBeenCalledTimes(1);
  });
});
