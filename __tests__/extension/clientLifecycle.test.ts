// Unit tests for initializeClient / stopClient on the Waterproof extension class.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// Which languages a build supports is now decided by the entry point: it hands
// over a `LanguageSupport`, and Lean is configured only when that record has a
// `lean` factory. What is covered here:
//   - a Rocq-only support record producing no Lean setup and no Lean server
//     config (the web extension),
//   - a full support record producing both, each with its own client options,
//   - the output channels being created lazily, so an unsupported language
//     leaves no empty channel behind,
//   - the web build skipping the prelaunch checks (they shell out through
//     child_process, which a web build cannot do),
//   - stopClient disposing a client that was created but never started.
//
// Like the event-handler tests, these invoke the (private) prototype methods
// with a hand-rolled `this` rather than constructing the whole extension.

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

import { window } from "vscode";
import { Waterproof } from "../../src/extension";
import { WaterproofConfigHelper } from "../../src/helpers";
import { LeanLspServerConfig } from "../../src/lsp-client/lean";
import {
  createdComposites,
  resetExtensionMocks,
} from "../__helpers__/extension-mocks";
import type {
  LanguageClientProviderFactory,
  LanguageSupport,
} from "../../src/lsp-client/clientTypes";

const createOutputChannel = window.createOutputChannel as jest.Mock;
const configGet = WaterproofConfigHelper.get as jest.Mock;
const leanConfigCreate = LeanLspServerConfig.create as jest.Mock;

/** A language-client provider factory that records how it was called. */
function makeFactory(): jest.Mock & LanguageClientProviderFactory {
  return jest.fn(() => jest.fn()) as unknown as jest.Mock &
    LanguageClientProviderFactory;
}

type Ctx = {
  context: Record<string, unknown>;
  languageSupport: LanguageSupport;
  _isWeb: boolean;
  client?: unknown;
  clientRunning: boolean;
  statusBar: { update: jest.Mock; failed: jest.Mock };
  webviewManager: { open: jest.Mock };
};

function makeCtx(overrides: Partial<Ctx> = {}): Ctx {
  return {
    context: {},
    languageSupport: { rocq: makeFactory() },
    _isWeb: false,
    client: undefined,
    clientRunning: false,
    statusBar: { update: jest.fn(), failed: jest.fn() },
    webviewManager: { open: jest.fn() },
    ...overrides,
  };
}

const proto = Waterproof.prototype as unknown as {
  initializeClient: (this: unknown) => Promise<void>;
  stopClient: (this: unknown) => Promise<void>;
};

/** The `LanguageClientSetups` that `initializeClient` built the composite from. */
function setups() {
  expect(createdComposites).toHaveLength(1);
  return createdComposites[0].setups;
}

beforeEach(() => {
  jest.clearAllMocks();
  resetExtensionMocks();
  configGet.mockReturnValue("none");
});

describe("initializeClient language wiring", () => {
  it("builds no Lean setup when the entry point supports only Rocq", async () => {
    const ctx = makeCtx({
      languageSupport: { rocq: makeFactory() },
      _isWeb: true,
    });

    await proto.initializeClient.call(ctx);

    expect(setups().rocq).toBeDefined();
    expect(setups().lean).toBeUndefined();
    // Nothing should even compute the Lean server options.
    expect(leanConfigCreate).not.toHaveBeenCalled();
  });

  it("creates no output channel for an unsupported language", async () => {
    const ctx = makeCtx({
      languageSupport: { rocq: makeFactory() },
      _isWeb: true,
    });

    await proto.initializeClient.call(ctx);

    // The channels are thunks the composite calls, so initializeClient itself
    // creates none; and there is no Lean thunk to call at all.
    expect(createOutputChannel).not.toHaveBeenCalled();
    expect(setups().rocq.createOutputChannel()).toEqual(
      expect.objectContaining({
        name: "Waterproof Rocq LSP Events (After Initialization)",
      }),
    );
  });

  it("builds both setups when the entry point supports Lean too", async () => {
    const rocq = makeFactory();
    const lean = makeFactory();

    await proto.initializeClient.call(
      makeCtx({ languageSupport: { rocq, lean } }),
    );

    expect(setups().lean).toBeDefined();
    expect(leanConfigCreate).toHaveBeenCalledTimes(1);
    expect(setups().lean?.createOutputChannel()).toEqual(
      expect.objectContaining({
        name: "Waterproof Lean LSP Events (After Initialization)",
      }),
    );
  });

  it("gives each factory its own language's client options", async () => {
    const rocq = makeFactory();
    const lean = makeFactory();
    const ctx = makeCtx({ languageSupport: { rocq, lean } });

    await proto.initializeClient.call(ctx);

    expect(rocq).toHaveBeenCalledTimes(1);
    expect(lean).toHaveBeenCalledTimes(1);
    expect(rocq.mock.calls[0][1]).toEqual(
      expect.objectContaining({
        documentSelector: [{ language: "markdown" }, { language: "coq" }],
      }),
    );
    expect(lean.mock.calls[0][1]).toEqual(
      expect.objectContaining({ documentSelector: [{ language: "lean4" }] }),
    );
    // Both are handed the extension context they were registered with.
    expect(rocq.mock.calls[0][0]).toBe(ctx.context);
  });

  it("passes each factory's provider to the matching setup", async () => {
    const rocqProvider = jest.fn();
    const rocq = jest.fn(
      () => rocqProvider,
    ) as unknown as LanguageClientProviderFactory;

    await proto.initializeClient.call(makeCtx({ languageSupport: { rocq } }));

    expect(setups().rocq.provider).toBe(rocqProvider);
  });
});

describe("initializeClient launch checks", () => {
  it("skips the prelaunch checks in the web build", async () => {
    configGet.mockReturnValue("none");
    const ctx = makeCtx({ _isWeb: true });

    await proto.initializeClient.call(ctx);

    const composite = ctx.client as {
      prelaunchChecks: jest.Mock;
      startWithHandlers: jest.Mock;
    };
    // The checks shell out through child_process, which a web build cannot do.
    expect(composite.prelaunchChecks).not.toHaveBeenCalled();
    expect(composite.startWithHandlers).toHaveBeenCalledWith(
      ctx.webviewManager,
      ["rocq"],
    );
  });

  it("runs the prelaunch checks on desktop when the user has not skipped them", async () => {
    configGet.mockReturnValue("none");
    const ctx = makeCtx({ _isWeb: false });

    await proto.initializeClient.call(ctx);

    const composite = ctx.client as { prelaunchChecks: jest.Mock };
    expect(composite.prelaunchChecks).toHaveBeenCalledTimes(1);
  });

  it("honours an explicit skip setting on desktop", async () => {
    configGet.mockReturnValue("all");
    const ctx = makeCtx({ _isWeb: false });

    await proto.initializeClient.call(ctx);

    const composite = ctx.client as {
      prelaunchChecks: jest.Mock;
      startWithHandlers: jest.Mock;
    };
    expect(composite.prelaunchChecks).not.toHaveBeenCalled();
    expect(composite.startWithHandlers).toHaveBeenCalledWith(
      ctx.webviewManager,
      ["rocq", "lean4"],
    );
  });
});

describe("stopClient", () => {
  function clientDouble(isRunning: boolean) {
    return {
      isRunning: jest.fn(() => isRunning),
      dispose: jest.fn(async () => {}),
    };
  }

  it("disposes a client that was created but never started", async () => {
    // Regression test: guarding on isRunning left such a client undisposed, so
    // the next initializeClient orphaned the resources it owned.
    const client = clientDouble(false);
    const ctx = makeCtx({ client, clientRunning: false });

    await proto.stopClient.call(ctx);

    expect(client.dispose).toHaveBeenCalledWith(2000);
  });

  it("does not report a stop for a client that was not running", async () => {
    const client = clientDouble(false);
    const ctx = makeCtx({ client, clientRunning: false });

    await proto.stopClient.call(ctx);

    expect(ctx.statusBar.update).not.toHaveBeenCalled();
  });

  it("disposes a running client and clears the status bar", async () => {
    const client = clientDouble(true);
    const ctx = makeCtx({ client, clientRunning: true });

    await proto.stopClient.call(ctx);

    expect(client.dispose).toHaveBeenCalledWith(2000);
    expect(ctx.clientRunning).toBe(false);
    expect(ctx.statusBar.update).toHaveBeenCalledWith([]);
  });
});
