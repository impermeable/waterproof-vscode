
jest.mock(
  "vscode",
  () => {
    const Position = class {
      constructor(
        public line: number,
        public character: number,
      ) {}
      translate(lineDelta: number, charDelta: number) {
        return new Position(this.line + lineDelta, this.character + charDelta);
      }
      isAfter(other: InstanceType<typeof Position>) {
        return (
          this.line > other.line ||
          (this.line === other.line && this.character > other.character)
        );
      }
      isBeforeOrEqual(other: InstanceType<typeof Position>) {
        return !this.isAfter(other);
      }
    };

    const Range = class {
      constructor(
        public start: InstanceType<typeof Position>,
        public end: InstanceType<typeof Position>,
      ) {}
      intersection(
        other: InstanceType<typeof Range>,
      ): InstanceType<typeof Range> | undefined {
        const startLine = Math.max(this.start.line, other.start.line);
        const endLine = Math.min(this.end.line, other.end.line);
        if (startLine > endLine) return undefined;
        return new Range(new Position(startLine, 0), new Position(endLine, 0));
      }
      get isEmpty() {
        return (
          this.start.line === this.end.line &&
          this.start.character === this.end.character
        );
      }
    };

    const CancellationTokenSource = class {
      private listeners: Array<() => void> = [];

      token = {
        isCancellationRequested: false,
        onCancellationRequested: (listener: () => void) => {
          this.listeners.push(listener);
          return {
            dispose: () => {
              this.listeners = this.listeners.filter(
                (item) => item !== listener,
              );
            },
          };
        },
      };

      cancel() {
        this.token.isCancellationRequested = true;
        this.listeners.forEach((listener) => listener());
      }

      dispose() {
        this.listeners = [];
      }
    };

    return {
      Position,
      Range,
      CancellationTokenSource,
      DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2, Hint: 3 },
      EventEmitter: class {
        fire() {}
        event = () => ({ dispose: () => {} });
      },
      workspace: {
        getConfiguration: jest.fn(() => ({
          get: jest.fn((_key: string, def?: unknown) => def),
        })),
        onDidChangeConfiguration: jest.fn(() => ({ dispose: jest.fn() })),
        onDidChangeTextDocument: jest.fn(() => ({ dispose: jest.fn() })),
      },
      languages: {
        createDiagnosticCollection: jest.fn(() => ({
          set: jest.fn(),
          dispose: jest.fn(),
        })),
        getDiagnostics: jest.fn(() => []),
        onDidChangeDiagnostics: jest.fn(() => ({ dispose: jest.fn() })),
      },
      window: {
        createOutputChannel: jest.fn(() => ({
          appendLine: jest.fn(),
          dispose: jest.fn(),
        })),
      },
    };
  },
  { virtual: true },
);

jest.mock(
  "vscode-languageclient",
  () => ({
    LogTraceNotification: { type: "$/logTrace" },
    RequestType: jest.fn().mockImplementation(() => ({})),
    NotificationType: jest.fn().mockImplementation(() => ({})),
    DocumentSymbolRequest: { type: {} },
    CodeActionRequest: { type: { method: "textDocument/codeAction" } },
  }),
  { virtual: true },
);

jest.mock(
  "vscode-languageserver-types",
  () => ({
    VersionedTextDocumentIdentifier: {
      create: jest.fn((uri, v) => ({ uri, version: v })),
    },
  }),
  { virtual: true },
);

jest.mock(
  "@impermeable/waterproof-editor",
  () => ({
    InputAreaStatus: {
      Correct: "Correct",
      Incorrect: "Incorrect",
      Invalid: "Invalid",
    },
    Severity: {
      Error: 0,
      Warning: 1,
      Information: 2,
      Hint: 3,
    },
  }),
  { virtual: true },
);
jest.mock("@leanprover/infoview-api", () => ({}), { virtual: true });
jest.mock(
  "../../src/lsp-client/lean/converter",
  () => ({ patchDiagnosticConverters: jest.fn() }),
  { virtual: true },
);

jest.mock("../../src/lsp-client/lean/requestTypes", () => ({
  leanFileProgressNotificationType: { type: "$/lean/fileProgress" },
  leanGoalRequestType: { type: "$/lean/goal" },
  LeanTag: { UnsolvedGoals: "UnsolvedGoals" },
  LeanPublishDiagnosticsParams: {},
}));

import {
  Range,
  Position,
  DiagnosticSeverity,
  TextDocument,
  OutputChannel,
  Uri,
  Diagnostic,
  languages,
} from "vscode";
import { LanguageClientProvider } from "../../src/lsp-client/clientTypes";
import { LeanLspClient } from "../../src/lsp-client/lean";
import { WebviewManager } from "../../src/webviewManager";
import { MessageType } from "../../shared";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const FAKE_DOCUMENT = {
  uri: { toString: () => "file:///test.lean", path: "/test.lean" },
  version: 1,
  getText: () => ":::input\n\n:::\n",
  offsetAt: (pos: Position) => pos.line * 100 + pos.character,
  positionAt: (offset: number) =>
    new Position(Math.floor(offset / 100), offset % 100),
  lineCount: 10,
} as TextDocument;

function makeClientDouble() {
  return {
    isRunning: jest.fn(() => true),
    start: jest.fn(() => Promise.resolve()),
    dispose: jest.fn(() => Promise.resolve()),
    onNotification: jest.fn(() => ({ dispose: jest.fn() })),
    sendRequest: jest.fn().mockResolvedValue([]),
    middleware: { handleDiagnostics: undefined },
    protocol2CodeConverter: {
      asRange: (r: Range) => r,
      asWorkspaceEdit: jest.fn(async (edit: unknown) => edit),
    },
    code2ProtocolConverter: {
      asUri: (u: Uri) => u.toString(),
      asDiagnostic: (d: Diagnostic) => d,
      asRange: (range: Range) => range,
      asDiagnostics: jest.fn(async (diagnostics: Diagnostic[]) => diagnostics),
    },
  };
}

function makeClient(isBusy = false) {
  const clientDouble = makeClientDouble();
  const instance = new LeanLspClient(
    jest.fn(() => clientDouble) as unknown as LanguageClientProvider,
    { appendLine: jest.fn() } as unknown as OutputChannel,
  );
  instance.activeDocument = FAKE_DOCUMENT;
  instance.webviewManager = {
    postMessage: jest.fn(),
    postAndCacheMessage: jest.fn(),
    has: jest.fn(() => true),
  } as unknown as WebviewManager;
  // @ts-expect-error private
  instance.isBusy = isBusy;
  return instance;
}

// ===========================================================================
// Tests
// ===========================================================================
describe("LspClient.processDiagnostics code actions", () => {
  const getDiagnostics =
    languages.getDiagnostics as unknown as jest.MockedFunction<
      (uri: Uri) => Diagnostic[]
    >;

  const infoDiagnostic = (): Diagnostic =>
    ({
      message: "Help",
      severity: DiagnosticSeverity.Information,
      range: new Range(new Position(1, 2), new Position(1, 6)),
    }) as Diagnostic;

  const processDiagnostics = (instance: LeanLspClient) => {
    // @ts-expect-error protected
    return instance.processDiagnostics();
  };

  /** Pulls every `codeActionsResolved` patch sent to the webview, across all postMessage calls. */
  const resolvedPatches = (instance: LeanLspClient) => {
    const postMessage = instance.webviewManager?.postMessage as jest.Mock;
    return postMessage.mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.codeActionsResolved);
  };

  /** Pulls every base-diagnostics message sent to the webview. */
  const diagnosticsMessages = (instance: LeanLspClient) => {
    const postAndCache = instance.webviewManager
      ?.postAndCacheMessage as jest.Mock;
    return postAndCache.mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.diagnostics);
  };

  beforeEach(() => {
    getDiagnostics.mockReturnValue([]);
  });

  it("shows diagnostics right away, without waiting for code actions to resolve", async () => {
    const diagnostic = infoDiagnostic();
    getDiagnostics.mockReturnValue([diagnostic]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    // Code action resolution never resolves during this test - diagnostics must
    // still be delivered without waiting on it.
    sendRequest.mockImplementation(() => new Promise(() => {}));

    // Intentionally not awaited: processDiagnostics only resolves once code-action
    // resolution finishes, which this test deliberately never does.
    void processDiagnostics(instance);

    // Flush all pending microtasks
    await new Promise((resolve) => setImmediate(resolve));

    const messages = diagnosticsMessages(instance);
    expect(messages).toHaveLength(1);
    expect(messages[0].body.positionedDiagnostics).toEqual([
      expect.objectContaining({
        message: "Help",
        startOffset: 102,
        endOffset: 106,
      }),
    ]);
  });

  it("delivers a resolved code action attached to the diagnostic it belongs to", async () => {
    const diagnostic = infoDiagnostic();
    getDiagnostics.mockReturnValue([diagnostic]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Try this: exact h", edit: { changes: {} } },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(3, 4), new Position(3, 8)),
              newText: "exact h",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    const patches = resolvedPatches(instance);
    expect(patches).toEqual([
      expect.objectContaining({
        body: expect.objectContaining({
          index: 0,
          codeActions: [
            {
              title: "Try this: exact h",
              edits: [{ start: 304, end: 308, newText: "exact h" }],
            },
          ],
        }),
      }),
    ]);
  });

  it("never delivers code actions from a pass superseded by a newer one", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    let resolveFirst!: (value: unknown[]) => void;
    sendRequest
      .mockImplementationOnce(
        () =>
          new Promise((resolve) => {
            resolveFirst = resolve;
          }),
      )
      .mockResolvedValueOnce([]);

    const firstPass = processDiagnostics(instance);
    const secondPass = processDiagnostics(instance);

    await secondPass;
    resolveFirst([{ title: "Stale fix", edit: { changes: {} } }]);
    await firstPass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("never delivers code actions once the client has been disposed", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    let resolveRequest!: (value: unknown[]) => void;
    sendRequest.mockImplementationOnce(
      () =>
        new Promise((resolve) => {
          resolveRequest = resolve;
        }),
    );

    const diagnosticsPass = processDiagnostics(instance);

    await instance.dispose();
    resolveRequest([{ title: "Late fix", edit: { changes: {} } }]);
    await diagnosticsPass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  // ---- resolveCodeActionsFor selection logic --------

  it("prefers the action explicitly marked isPreferred over other valid actions", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    const makeEdit = (text: string) => ({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: text,
            },
          ],
        ],
      ],
    });
    sendRequest.mockResolvedValue([
      { title: "Option A", edit: { changes: {} } },
      { title: "Option B", edit: { changes: {} }, isPreferred: true },
    ]);
    asWorkspaceEdit
      .mockResolvedValueOnce(makeEdit("a"))
      .mockResolvedValueOnce(makeEdit("b"));

    await processDiagnostics(instance);

    const patches = resolvedPatches(instance);
    expect(patches[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Option B" }),
    ]);
  });

  it("returns no code action when multiple valid actions exist and none is preferred", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    const makeEdit = (text: string) => ({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: text,
            },
          ],
        ],
      ],
    });
    sendRequest.mockResolvedValue([
      { title: "Option A", edit: { changes: {} } },
      { title: "Option B", edit: { changes: {} } },
    ]);
    asWorkspaceEdit
      .mockResolvedValueOnce(makeEdit("a"))
      .mockResolvedValueOnce(makeEdit("b"));

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("skips command-only results that have no edit", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Run command", command: { command: "noop", title: "noop" } },
    ]);

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("skips disabled code actions", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Disabled", edit: { changes: {} }, disabled: { reason: "n/a" } },
    ]);

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("skips an action whose edit touches more than one document", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Cross-file fix", edit: { changes: {} } },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: "x",
            },
          ],
        ],
        [
          { toString: () => "file:///other.lean" },
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: "y",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("recovers and still shows diagnostics when the code action request throws", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockRejectedValue(new Error("server exploded"));

    await expect(processDiagnostics(instance)).resolves.toBeUndefined();
    expect(diagnosticsMessages(instance)).toHaveLength(1);
    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("does nothing when there is no active document", async () => {
    const instance = makeClient();
    instance.activeDocument = undefined;
    const postAndCache = instance.webviewManager!
      .postAndCacheMessage as jest.Mock;
    const postMessage = instance.webviewManager!.postMessage as jest.Mock;

    await processDiagnostics(instance);

    expect(postAndCache).not.toHaveBeenCalled();
    expect(postMessage).not.toHaveBeenCalled();
  });

  it("maps each vscode diagnostic severity to the corresponding waterproof severity", async () => {
    const mk = (message: string, severity: DiagnosticSeverity) =>
      ({
        message,
        severity,
        range: new Range(new Position(0, 0), new Position(0, 1)),
      }) as Diagnostic;

    getDiagnostics.mockReturnValue([
      mk("e", DiagnosticSeverity.Error),
      mk("w", DiagnosticSeverity.Warning),
      mk("i", DiagnosticSeverity.Information),
      mk("h", DiagnosticSeverity.Hint),
    ]);
    const instance = makeClient();
    (instance.client.sendRequest as jest.Mock).mockResolvedValue([]);

    await processDiagnostics(instance);

    const [message] = diagnosticsMessages(instance);
    expect(
      message.body.positionedDiagnostics.map(
        (d: { severity: number }) => d.severity,
      ),
    ).toEqual([0, 1, 2, 3]);
  });

  it("tags a resolved-code-action patch with the correct index among several diagnostics", async () => {
    const diagA = infoDiagnostic();
    const diagB = { ...infoDiagnostic(), message: "Help 2" };
    getDiagnostics.mockReturnValue([diagA, diagB]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest
      .mockResolvedValueOnce([]) // diagA: no valid action
      .mockResolvedValueOnce([{ title: "Fix B", edit: { changes: {} } }]); // diagB
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: "b",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    const patches = resolvedPatches(instance);
    expect(patches).toHaveLength(1);
    expect(patches[0].body.index).toBe(1);
  });

  it("delivers a fast-resolving diagnostic's code action without waiting on a slower one", async () => {
    const diagA = infoDiagnostic();
    const diagB = { ...infoDiagnostic(), message: "Help 2" };
    getDiagnostics.mockReturnValue([diagA, diagB]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    let resolveSlow!: (v: unknown[]) => void;
    sendRequest
      .mockImplementationOnce(
        () =>
          new Promise((resolve) => {
            resolveSlow = resolve;
          }),
      ) // diagA: slow
      .mockResolvedValueOnce([{ title: "Fast fix", edit: { changes: {} } }]); // diagB: fast
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: "x",
            },
          ],
        ],
      ],
    });

    const pass = processDiagnostics(instance);
    // Flush microtasks so the already-resolved (fast) diagnostic's patch can
    // land, while the slow one is still deliberately unresolved.
    await new Promise((resolve) => setImmediate(resolve));

    expect(resolvedPatches(instance)).toEqual([
      expect.objectContaining({ body: expect.objectContaining({ index: 1 }) }),
    ]);

    resolveSlow([]);
    await pass;
  });

  it("drops a resolved code-action patch when the document version changes before it resolves", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const doc = { ...FAKE_DOCUMENT, version: 1 } as TextDocument;
    instance.activeDocument = doc;
    const sendRequest = instance.client.sendRequest as jest.Mock;
    let resolveRequest!: (v: unknown[]) => void;
    sendRequest.mockImplementationOnce(
      () =>
        new Promise((resolve) => {
          resolveRequest = resolve;
        }),
    );

    const pass = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve)); // let it reach sendRequest

    (doc as { version: number }).version = 2; // simulate an edit mid-flight

    resolveRequest([{ title: "Now-stale fix", edit: { changes: {} } }]);
    await pass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("drops a resolved code-action patch when the active document changes before it resolves", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    let resolveRequest!: (v: unknown[]) => void;
    sendRequest.mockImplementationOnce(
      () =>
        new Promise((resolve) => {
          resolveRequest = resolve;
        }),
    );

    const pass = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve));

    instance.activeDocument = {
      ...FAKE_DOCUMENT,
      uri: { toString: () => "file:///switched.lean", path: "/switched.lean" },
    } as TextDocument;

    resolveRequest([{ title: "Now-stale fix", edit: { changes: {} } }]);
    await pass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });
});
