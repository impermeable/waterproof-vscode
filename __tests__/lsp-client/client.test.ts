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
      contains(
        other: InstanceType<typeof Range> | InstanceType<typeof Position>,
      ) {
        const start = "start" in other ? other.start : other;
        const end = "end" in other ? other.end : other;
        return !this.start.isAfter(start) && !end.isAfter(this.end);
      }
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
import { LspClient } from "../../src/lsp-client/client";
import { WebviewManager } from "../../src/webviewManager";
import { MessageType } from "../../shared";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import type { GoalAnswer, GoalRequest } from "../../lib/types";
import type { CodeAction } from "vscode-languageclient";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const FAKE_TEXT = ":::input\nline one\nline two\nline three\nline four\n:::\n";

function computeLineStarts(text: string): number[] {
  const starts = [0];
  for (let i = 0; i < text.length; i++) {
    if (text[i] === "\n") starts.push(i + 1);
  }
  return starts;
}
const LINE_STARTS = computeLineStarts(FAKE_TEXT);

const FAKE_DOCUMENT = {
  uri: { toString: () => "file:///test.wp", path: "/test.wp" },
  version: 1,
  getText: () => FAKE_TEXT,
  offsetAt: (pos: Position) => LINE_STARTS[pos.line] + pos.character,
  positionAt: (offset: number) => {
    let line = 0;
    for (let i = 0; i < LINE_STARTS.length; i++) {
      if (LINE_STARTS[i] <= offset) line = i;
      else break;
    }
    return new Position(line, offset - LINE_STARTS[line]);
  },
  lineCount: 6,
} as TextDocument;

// A document with two separate input areas, separated by non-input text:
//   line 0: :::input
//   line 1: first area line     <- inside area 1
//   line 2: :::
//   line 3: non-input text
//   line 4: :::input
//   line 5: second area line    <- inside area 2
//   line 6: :::
const MULTI_AREA_TEXT =
  ":::input\nfirst area line\n:::\nnon-input text\n:::input\nsecond area line\n:::\n";
const MULTI_AREA_LINE_STARTS = computeLineStarts(MULTI_AREA_TEXT);

const MULTI_AREA_DOCUMENT = {
  uri: { toString: () => "file:///multi.wp", path: "/multi.wp" },
  version: 1,
  getText: () => MULTI_AREA_TEXT,
  offsetAt: (pos: Position) => MULTI_AREA_LINE_STARTS[pos.line] + pos.character,
  positionAt: (offset: number) => {
    let line = 0;
    for (let i = 0; i < MULTI_AREA_LINE_STARTS.length; i++) {
      if (MULTI_AREA_LINE_STARTS[i] <= offset) line = i;
      else break;
    }
    return new Position(line, offset - MULTI_AREA_LINE_STARTS[line]);
  },
  lineCount: 7,
} as TextDocument;

/**
 * A minimal, entirely test-owned concrete subclass of the abstract `LspClient`.
 *
 * This exists purely to exercise the base-class behaviour (diagnostics
 * processing, code action resolution/filtering, input-area matching, ...)
 * without depending on any real language client. It defines its own
 * `isAllowedCodeAction`, independent of any language-specific rule, so we
 * can verify that `resolveCodeActionsFor` actually honors whatever a
 * subclass decides to allow: here, only actions explicitly tagged as
 * `kind: "quickfix"` are allowed through.
 *
 * `getInputAreas` recognizes simple ":::input" / ":::" delimited blocks,
 * matching the fixture documents defined above (`FAKE_DOCUMENT`,
 * `MULTI_AREA_DOCUMENT`).
 */
class TestLspClient extends LspClient<GoalRequest, GoalAnswer> {
  readonly language = "test-lang";

  protected isAllowedCodeAction(result: CodeAction): boolean {
    return result.kind === "quickfix";
  }

  protected getInputAreas(document: TextDocument): Range[] | undefined {
    const lines = document.getText().split("\n");
    const areas: Range[] = [];
    let openLine: number | undefined;

    lines.forEach((line, i) => {
      if (line.trim() === ":::input") {
        openLine = i;
      } else if (line.trim() === ":::" && openLine !== undefined) {
        areas.push(new Range(new Position(openLine, 0), new Position(i, 0)));
        openLine = undefined;
      }
    });

    return areas;
  }

  protected async determineProofStatus(): Promise<InputAreaStatus> {
    // Not exercised by these tests; a constant is sufficient.
    return InputAreaStatus.Correct;
  }

  createGoalsRequestParameters(
    document: TextDocument,
    position: Position,
  ): GoalRequest {
    return {
      textDocument: VersionedTextDocumentIdentifier.create(
        document.uri.toString(),
        document.version,
      ),
      position,
    };
  }

  requestGoals(
    _parametersOrPosition?: GoalRequest | Position,
  ): Promise<GoalAnswer | null> {
    return Promise.resolve(null);
  }

  async sendViewportHint(): Promise<void> {
    /* no-op: not exercised by these tests */
  }
}

function makeClientDouble(overrides: { sendRequest?: jest.Mock } = {}) {
  return {
    isRunning: jest.fn(() => true),
    start: jest.fn(() => Promise.resolve()),
    dispose: jest.fn(() => Promise.resolve()),
    onNotification: jest.fn(() => ({ dispose: jest.fn() })),
    sendRequest: overrides.sendRequest ?? jest.fn().mockResolvedValue([]),
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

function makeClient(overrides: { sendRequest?: jest.Mock } = {}) {
  const clientDouble = makeClientDouble(overrides);
  const instance = new TestLspClient(
    jest.fn(() => clientDouble) as unknown as LanguageClientProvider,
    { appendLine: jest.fn() } as unknown as OutputChannel,
  );
  instance.activeDocument = FAKE_DOCUMENT;
  instance.webviewManager = {
    postMessage: jest.fn(),
    postAndCacheMessage: jest.fn(),
    cacheMessage: jest.fn(),
    has: jest.fn(() => true),
  } as unknown as WebviewManager;
  return instance;
}

/**
 * A fake LSP server for testing cancellation end-to-end.
 */
class MockCodeActionServer {
  private resolvers: Array<(v: unknown) => void> = [];
  private settled: boolean[] = [];

  /** Indices, in request order, of requests the server cancelled before a test ever got to `respond` to them. */
  readonly cancelledRequests: number[] = [];

  sendRequest = jest.fn(
    (
      _type: unknown,
      _params: unknown,
      token: { onCancellationRequested: (cb: () => void) => unknown },
    ) => {
      const index = this.resolvers.length;
      this.settled.push(false);

      return new Promise((resolve, reject) => {
        this.resolvers.push(resolve);
        if (!token) return;
        token.onCancellationRequested(() => {
          if (this.settled[index]) return;
          this.settled[index] = true;
          this.cancelledRequests.push(index);
          reject({ message: "Request got old in server" });
        });
      });
    },
  );

  /** Simulates the server answering the Nth request it received. A no-op if the server already settled/cancelled it. */
  respond(index: number, actions: unknown[]): void {
    if (this.settled[index]) return;
    this.settled[index] = true;
    this.resolvers[index](actions);
  }
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

  const processDiagnostics = (instance: TestLspClient) => {
    // @ts-expect-error protected
    return instance.processDiagnostics();
  };

  /** Pulls every `codeActionsResolved` patch sent to the webview, across all postMessage calls. */
  const resolvedPatches = (instance: TestLspClient) => {
    const postMessage = instance.webviewManager?.postMessage as jest.Mock;
    return postMessage.mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.codeActionsResolved);
  };

  /** Pulls every base-diagnostics message sent to the webview. */
  const diagnosticsMessages = (instance: TestLspClient) => {
    const postAndCache = instance.webviewManager
      ?.postAndCacheMessage as jest.Mock;
    return postAndCache.mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.diagnostics);
  };

  /** Pulls every message passed to the (cache-only, not re-posted) cacheMessage call. */
  const cachedMessages = (instance: TestLspClient) => {
    const cacheMessage = instance.webviewManager?.cacheMessage as jest.Mock;
    return cacheMessage.mock.calls
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
        startOffset: 11,
        endOffset: 15,
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
      {
        title: "Try this: exact h",
        edit: { changes: {} },
        kind: "quickfix",
      },
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
              edits: [{ start: 31, end: 35, newText: "exact h" }],
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
    resolveFirst([
      { title: "Stale fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
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
    await new Promise((resolve) => setImmediate(resolve)); // let it reach sendRequest

    await instance.dispose();
    resolveRequest([
      { title: "Late fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
    await diagnosticsPass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  // ---- cancellation, end-to-end against a fake server --------

  it("delivers the code action normally when the server answers before anything supersedes or disposes the request", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const server = new MockCodeActionServer();
    const instance = makeClient({ sendRequest: server.sendRequest });
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
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
    await new Promise((resolve) => setImmediate(resolve)); // let the request reach the server
    server.respond(0, [
      { title: "Fine", edit: { changes: {} }, kind: "quickfix" },
    ]);
    await pass;

    expect(server.cancelledRequests).toEqual([]);
    expect(resolvedPatches(instance)[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Fine" }),
    ]);
  });

  it("never delivers code actions from a pass the server itself cancelled because a newer pass superseded it", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const server = new MockCodeActionServer();
    const instance = makeClient({ sendRequest: server.sendRequest });

    const firstPass = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve)); // let the first request reach the server

    const secondPass = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve)); // let the second request reach the server

    // The server itself noticed the first request's token was cancelled -
    // this is observed behaviour, not an inspection of mock call args.
    expect(server.cancelledRequests).toEqual([0]);

    // Even if the (real) server raced and tried to answer the already-cancelled
    // request anyway, the client must not surface it.
    server.respond(0, [
      { title: "Stale fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
    server.respond(1, []);
    await Promise.all([firstPass, secondPass]);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("cancels the in-flight request at the server when the client is disposed, and never delivers its result", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const server = new MockCodeActionServer();
    const instance = makeClient({ sendRequest: server.sendRequest });

    const pass = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve)); // let the request reach the server

    expect(server.cancelledRequests).toEqual([]);

    await instance.dispose();

    expect(server.cancelledRequests).toEqual([0]);

    // Even a late answer from the server must not reach the webview.
    server.respond(0, [
      { title: "Late fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
    await pass;

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
      { title: "Option A", edit: { changes: {} }, kind: "quickfix" },
      {
        title: "Option B",
        edit: { changes: {} },
        isPreferred: true,
        kind: "quickfix",
      },
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

  it("skips an action whose edit touches more than one document", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Cross-file fix", edit: { changes: {} }, kind: "quickfix" },
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
          { toString: () => "file:///other.wp" },
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
      .mockResolvedValueOnce([
        {
          title: "Fix B",
          edit: { changes: {} },
          kind: "quickfix",
        },
      ]); // diagB
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
      .mockResolvedValueOnce([
        {
          title: "Fast fix",
          edit: { changes: {} },
          kind: "quickfix",
        },
      ]); // diagB: fast
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

    resolveRequest([
      { title: "Now-stale fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
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
      uri: { toString: () => "file:///switched.wp", path: "/switched.wp" },
    } as TextDocument;

    resolveRequest([
      { title: "Now-stale fix", edit: { changes: {} }, kind: "quickfix" },
    ]);
    await pass;

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("drops an action when its edit reaches outside the containing input area", async () => {
    // The input area spans lines 0–5 (up to the ':::' closing marker at line 5).
    // This edit targets the closing marker itself, i.e. just past areaEnd.
    getDiagnostics.mockReturnValue([infoDiagnostic()]); // range (1,2)-(1,6), inside the area
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest.mockResolvedValue([
      {
        title: "Reaches past the area",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              // line 5 starts exactly at areaEnd; editing into it goes outside the area.
              range: new Range(new Position(5, 0), new Position(5, 3)),
              newText: "xxx",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("keeps an edit that lands exactly on the input area boundary", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest.mockResolvedValue([
      {
        title: "Stays inside",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              // Ends exactly at areaEnd (offset 48 / line 5, char 0) - should be kept.
              range: new Range(new Position(4, 0), new Position(5, 0)),
              newText: "y",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    const patches = resolvedPatches(instance);
    expect(patches[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Stays inside" }),
    ]);
  });

  it("caps preferred actions at 3 as well, when more than 3 are marked preferred", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest.mockResolvedValue(
      Array.from({ length: 4 }, (_, i) => ({
        title: `Preferred ${i + 1}`,
        edit: { changes: {} },
        isPreferred: true,
        kind: "quickfix",
      })),
    );
    asWorkspaceEdit.mockImplementation(async () => ({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(1, 0), new Position(1, 1)),
              newText: "z",
            },
          ],
        ],
      ],
    }));

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)[0].body.codeActions).toHaveLength(3);
  });

  it("skips resolving code actions entirely for a diagnostic outside every input area", async () => {
    // Range (10, 0)-(10, 1) is well past the document's only input area (lines 0-5).
    const outsideDiagnostic = {
      message: "Outside",
      severity: DiagnosticSeverity.Information,
      range: new Range(new Position(10, 0), new Position(10, 1)),
    } as Diagnostic;
    getDiagnostics.mockReturnValue([outsideDiagnostic]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;

    await processDiagnostics(instance);

    expect(sendRequest).not.toHaveBeenCalled();
    expect(resolvedPatches(instance)).toHaveLength(0);
    // Base diagnostics still get sent, just with no attached code actions.
    expect(diagnosticsMessages(instance)).toHaveLength(1);
  });

  // ---- isAllowedCodeAction (subclass-defined filtering is honored) --------
  //
  // `TestLspClient` overrides `isAllowedCodeAction` with a rule that is entirely
  // its own (only `kind: "quickfix"` actions are allowed) rather than any real
  // language client's rule. These tests confirm `resolveCodeActionsFor` actually
  // calls into and respects that override.

  it("filters out a code action whose kind is not quickfix", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Unrelated suggestion",
        edit: { changes: {} },
        kind: "refactor",
      },
    ]);

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("filters out a code action with no kind at all", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "No kind data", edit: { changes: {} } },
    ]);

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("allows a code action whose kind is exactly quickfix", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Quickfix: exact h",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(1, 0), new Position(1, 1)),
              newText: "exact h",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Quickfix: exact h" }),
    ]);
  });

  it("skips disabled code actions", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Disabled",
        edit: { changes: {} },
        disabled: { reason: "n/a" },
        kind: "quickfix",
      },
    ]);

    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(1, 0), new Position(1, 1)),
              newText: "should never be applied",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("keeps only the allowed action out of a mixed batch of quickfix and non-quickfix actions", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      { title: "Refactor suggestion", edit: { changes: {} }, kind: "refactor" },
      { title: "Quickfix suggestion", edit: { changes: {} }, kind: "quickfix" },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              range: new Range(new Position(1, 0), new Position(1, 1)),
              newText: "x",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Quickfix suggestion" }),
    ]);
  });

  it("matches each diagnostic to its own containing area when multiple input areas exist", async () => {
    const diagInAreaOne = {
      message: "Area one",
      severity: DiagnosticSeverity.Information,
      range: new Range(new Position(1, 0), new Position(1, 5)),
    } as Diagnostic;
    const diagInAreaTwo = {
      message: "Area two",
      severity: DiagnosticSeverity.Information,
      range: new Range(new Position(5, 0), new Position(5, 5)),
    } as Diagnostic;
    getDiagnostics.mockReturnValue([diagInAreaOne, diagInAreaTwo]);

    const instance = makeClient();
    instance.activeDocument = MULTI_AREA_DOCUMENT;
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    // Edits scoped to each area's own line, so a mis-attributed area (e.g. diagnostic 2
    // getting matched against area 1's bounds) would fail the "inside area" check and be
    // dropped, revealing incorrect area-to-diagnostic matching.
    sendRequest
      .mockResolvedValueOnce([
        { title: "Fix one", edit: { changes: {} }, kind: "quickfix" },
      ])
      .mockResolvedValueOnce([
        { title: "Fix two", edit: { changes: {} }, kind: "quickfix" },
      ]);
    asWorkspaceEdit
      .mockResolvedValueOnce({
        entries: () => [
          [
            MULTI_AREA_DOCUMENT.uri,
            [
              {
                range: new Range(new Position(1, 0), new Position(1, 1)),
                newText: "x",
              },
            ],
          ],
        ],
      })
      .mockResolvedValueOnce({
        entries: () => [
          [
            MULTI_AREA_DOCUMENT.uri,
            [
              {
                range: new Range(new Position(5, 0), new Position(5, 1)),
                newText: "y",
              },
            ],
          ],
        ],
      });

    await processDiagnostics(instance);

    const patches = resolvedPatches(instance);
    expect(patches).toHaveLength(2);
    expect(patches.find((p) => p.body.index === 0)?.body.codeActions).toEqual([
      expect.objectContaining({ title: "Fix one" }),
    ]);
    expect(patches.find((p) => p.body.index === 1)?.body.codeActions).toEqual([
      expect.objectContaining({ title: "Fix two" }),
    ]);
  });

  it("drops an action whose edit resolves to no text edits at all", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Empty edit",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    // Entries reference the right document but carry no actual text edits.
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [[FAKE_DOCUMENT.uri, []]],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)).toHaveLength(0);
  });

  it("keeps an edit that starts exactly on the input area's start boundary", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Starts at area start",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    asWorkspaceEdit.mockResolvedValue({
      entries: () => [
        [
          FAKE_DOCUMENT.uri,
          [
            {
              // Input area starts at offset 0 (line 0, char 0); this edit starts exactly there.
              range: new Range(new Position(0, 0), new Position(0, 1)),
              newText: "z",
            },
          ],
        ],
      ],
    });

    await processDiagnostics(instance);

    expect(resolvedPatches(instance)[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Starts at area start" }),
    ]);
  });

  it("still delivers a later diagnostic's code action when an earlier one's resolution throws", async () => {
    const diagA = infoDiagnostic();
    const diagB = { ...infoDiagnostic(), message: "Help 2" };
    getDiagnostics.mockReturnValue([diagA, diagB]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest
      .mockRejectedValueOnce(new Error("server exploded for diagA"))
      .mockResolvedValueOnce([
        {
          title: "Fix B",
          edit: { changes: {} },
          kind: "quickfix",
        },
      ]);
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

    await expect(processDiagnostics(instance)).resolves.toBeUndefined();

    const patches = resolvedPatches(instance);
    expect(patches).toHaveLength(1);
    expect(patches[0].body.index).toBe(1);
    expect(patches[0].body.codeActions).toEqual([
      expect.objectContaining({ title: "Fix B" }),
    ]);
    // Base diagnostics for both still went out despite diagA's failure.
    expect(diagnosticsMessages(instance)).toHaveLength(1);
  });

  // ---- caching the final diagnostics + code actions message --------

  it("caches the final diagnostics message (with resolved code actions) once any action resolves", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    sendRequest.mockResolvedValue([
      {
        title: "Try this: exact h",
        edit: { changes: {} },
        kind: "quickfix",
      },
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

    const cached = cachedMessages(instance);
    expect(cached).toHaveLength(1);
    expect(cached[0].body.positionedDiagnostics).toEqual([
      expect.objectContaining({
        message: "Help",
        codeActions: [expect.objectContaining({ title: "Try this: exact h" })],
      }),
    ]);
    // The cache update is a separate call from the initial (uncached-actions) base send.
    const postAndCache = instance.webviewManager!
      .postAndCacheMessage as jest.Mock;
    expect(postAndCache).toHaveBeenCalledTimes(1);
    const cacheMessage = instance.webviewManager!.cacheMessage as jest.Mock;
    expect(cacheMessage).toHaveBeenCalledTimes(1);
  });

  it("does not cache a final message when no code action resolves for any diagnostic", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    sendRequest.mockResolvedValue([]); // no valid actions

    await processDiagnostics(instance);

    expect(cachedMessages(instance)).toHaveLength(0);
  });

  it("does not cache a final message when the pass goes stale before any action resolves", async () => {
    getDiagnostics.mockReturnValue([infoDiagnostic()]);
    const instance = makeClient();
    const doc = { ...FAKE_DOCUMENT, version: 1 } as TextDocument;
    instance.activeDocument = doc;
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;
    let resolveRequest!: (v: unknown[]) => void;
    sendRequest.mockImplementationOnce(
      () =>
        new Promise((resolve) => {
          resolveRequest = resolve;
        }),
    );
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
    await new Promise((resolve) => setImmediate(resolve)); // let it reach sendRequest

    (doc as { version: number }).version = 2; // simulate an edit mid-flight, making this pass stale

    resolveRequest([
      {
        title: "Now-stale fix",
        edit: { changes: {} },
        kind: "quickfix",
      },
    ]);
    await pass;

    expect(cachedMessages(instance)).toHaveLength(0);
  });

  it("caches a single consolidated message with all code actions when several diagnostics resolve", async () => {
    const diagA = infoDiagnostic();
    const diagB = { ...infoDiagnostic(), message: "Help 2" };
    getDiagnostics.mockReturnValue([diagA, diagB]);
    const instance = makeClient();
    const sendRequest = instance.client.sendRequest as jest.Mock;
    const asWorkspaceEdit = instance.client.protocol2CodeConverter
      .asWorkspaceEdit as jest.Mock;

    sendRequest
      .mockResolvedValueOnce([
        { title: "Fix A", edit: { changes: {} }, kind: "quickfix" },
      ])
      .mockResolvedValueOnce([
        { title: "Fix B", edit: { changes: {} }, kind: "quickfix" },
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
      ],
    });

    await processDiagnostics(instance);

    const cached = cachedMessages(instance);
    expect(cached).toHaveLength(1);
    expect(cached[0].body.positionedDiagnostics).toEqual([
      expect.objectContaining({
        codeActions: [expect.objectContaining({ title: "Fix A" })],
      }),
      expect.objectContaining({
        codeActions: [expect.objectContaining({ title: "Fix B" })],
      }),
    ]);
  });
});
