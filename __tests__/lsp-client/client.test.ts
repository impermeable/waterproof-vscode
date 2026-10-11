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
import {
  LanguageClientProvider,
  SegmentedDiagnostic,
} from "../../src/lsp-client/clientTypes";
import { LspClient } from "../../src/lsp-client/client";
import { WebviewManager } from "../../src/webviewManager";
import { MessageType } from "../../shared";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import type { GoalAnswer, GoalRequest } from "../../lib/types";
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

/**
 * A minimal, entirely test-owned concrete subclass of the abstract `LspClient`.
 *
 * This exists purely to exercise the base-class behaviour (diagnostics
 * processing) without depending on any real language client.
 */
class TestLspClient extends LspClient<GoalRequest, GoalAnswer> {
  readonly language = "test-lang";

  protected getInputAreas(): Range[] | undefined {
    // Not exercised by these tests.
    return [];
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
    },
    code2ProtocolConverter: {
      asUri: (u: Uri) => u.toString(),
      asDiagnostic: (d: Diagnostic) => d,
      asRange: (range: Range) => range,
    },
  };
}

function makeClient() {
  const clientDouble = makeClientDouble();
  const instance = new TestLspClient(
    jest.fn(() => clientDouble) as unknown as LanguageClientProvider,
    { appendLine: jest.fn() } as unknown as OutputChannel,
  );
  instance.activeDocument = FAKE_DOCUMENT;
  instance.webviewManager = {
    postMessage: jest.fn(),
    postAndCacheMessage: jest.fn(),
    has: jest.fn(() => true),
  } as unknown as WebviewManager;
  return instance;
}

// ===========================================================================
// Tests
// ===========================================================================
describe("LspClient.processDiagnostics", () => {
  const getDiagnostics =
    languages.getDiagnostics as unknown as jest.MockedFunction<
      (uri: Uri) => Diagnostic[]
    >;

  const processDiagnostics = (instance: TestLspClient) => {
    // @ts-expect-error protected
    return instance.processDiagnostics();
  };

  /** Pulls every base-diagnostics message sent to the webview. */
  const diagnosticsMessages = (instance: TestLspClient) => {
    const postAndCache = instance.webviewManager
      ?.postAndCacheMessage as jest.Mock;
    return postAndCache.mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.diagnostics);
  };

  beforeEach(() => {
    getDiagnostics.mockReturnValue([]);
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

    await processDiagnostics(instance);

    const [message] = diagnosticsMessages(instance);
    expect(
      message.body.positionedDiagnostics.map(
        (d: { severity: number }) => d.severity,
      ),
    ).toEqual([0, 1, 2, 3]);
  });
});

describe("LspClient.processDiagnostics message segments", () => {
  const getDiagnostics =
    languages.getDiagnostics as unknown as jest.MockedFunction<
      (uri: Uri) => Diagnostic[]
    >;

  /** A test client that resolves message segments. */
  class SegmentTestClient extends TestLspClient {
    resolveSegments = jest.fn<
      Promise<SegmentedDiagnostic[] | undefined>,
      [TextDocument, readonly Diagnostic[]]
    >(async () => []);

    protected override resolveMessageSegments(
      document: TextDocument,
      diagnostics: readonly Diagnostic[],
    ) {
      return this.resolveSegments(document, diagnostics);
    }
  }

  function makeSegmentClient(document: TextDocument = FAKE_DOCUMENT) {
    const instance = new SegmentTestClient(
      jest.fn(() => makeClientDouble()) as unknown as LanguageClientProvider,
      { appendLine: jest.fn() } as unknown as OutputChannel,
    );
    instance.activeDocument = document;
    instance.webviewManager = {
      postMessage: jest.fn(),
      postAndCacheMessage: jest.fn(),
      has: jest.fn(() => true),
    } as unknown as WebviewManager;
    return instance;
  }

  const lspRange = (sl: number, sc: number, el: number, ec: number) => ({
    start: { line: sl, character: sc },
    end: { line: el, character: ec },
  });

  const HELP_MESSAGE = "Help\n  • We apply h";

  // "ne o" on line 1 ("line one", offsets 9..17) of FAKE_DOCUMENT.
  const helpDiagnostic = (message = HELP_MESSAGE): Diagnostic =>
    ({
      message,
      severity: DiagnosticSeverity.Information,
      range: new Range(new Position(1, 2), new Position(1, 6)),
    }) as Diagnostic;

  /** The help diagnostic, with a suggestion that replaces "line one" by "We apply h". */
  const segmentedHelp = (
    overrides: Partial<SegmentedDiagnostic> = {},
  ): SegmentedDiagnostic => ({
    range: lspRange(1, 2, 1, 6),
    message: HELP_MESSAGE,
    segments: [
      { text: "Help\n  • " },
      {
        text: "We apply h",
        edit: { range: lspRange(1, 0, 1, 8), newText: "We apply h" },
      },
    ],
    ...overrides,
  });

  const EXPECTED_SEGMENTS = [
    { text: "Help\n  • " },
    {
      text: "We apply h",
      edit: { start: 9, end: 17, newText: "We apply h", oldText: "line one" },
    },
  ];

  const processDiagnostics = (instance: TestLspClient) =>
    // @ts-expect-error protected
    instance.processDiagnostics();

  /** The `segments` of each diagnostic, per diagnostics message sent. */
  const sentSegments = (instance: TestLspClient) =>
    (instance.webviewManager?.postAndCacheMessage as jest.Mock).mock.calls
      .map(([, message]) => message)
      .filter((m) => m.type === MessageType.diagnostics)
      .map((m) =>
        m.body.positionedDiagnostics.map(
          (d: { segments?: unknown }) => d.segments,
        ),
      );

  beforeEach(() => {
    getDiagnostics.mockReturnValue([]);
  });

  it("shows diagnostics right away, without waiting for segments to resolve", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    // Segment resolution never finishes during this test.
    instance.resolveSegments.mockImplementation(() => new Promise(() => {}));

    void processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve));

    expect(sentSegments(instance)).toEqual([[undefined]]);
  });

  it("sends the diagnostics again with offset-based segments once they are resolved", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValue([segmentedHelp()]);

    await processDiagnostics(instance);

    expect(sentSegments(instance)).toEqual([[undefined], [EXPECTED_SEGMENTS]]);
    const postAndCache = instance.webviewManager!
      .postAndCacheMessage as jest.Mock;
    expect(postAndCache.mock.calls[1][1].body.version).toBe(1);
  });

  it("matches segmented diagnostics to published ones by range and message", async () => {
    getDiagnostics.mockReturnValue([
      helpDiagnostic(),
      helpDiagnostic("'help h' tactic does nothing"),
      {
        ...helpDiagnostic(),
        range: new Range(new Position(2, 2), new Position(2, 6)),
      } as Diagnostic,
    ]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValue([segmentedHelp()]);

    await processDiagnostics(instance);

    expect(sentSegments(instance)[1]).toEqual([
      EXPECTED_SEGMENTS,
      undefined,
      undefined,
    ]);
  });

  it("does not resolve segments when there are no diagnostics", async () => {
    const instance = makeSegmentClient();

    await processDiagnostics(instance);

    expect(instance.resolveSegments).not.toHaveBeenCalled();
    expect(sentSegments(instance)).toEqual([[]]);
  });

  it("does not send the diagnostics again when no diagnostic gets segments", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValue([]);

    await processDiagnostics(instance);

    expect(sentSegments(instance)).toEqual([[undefined]]);
  });

  it("sends nothing more when segments could not be resolved", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValue(undefined);

    await processDiagnostics(instance);

    expect(sentSegments(instance)).toEqual([[undefined]]);
  });

  it("logs and recovers when resolving segments fails", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockRejectedValue(new Error("rpc failed"));

    await expect(processDiagnostics(instance)).resolves.toBeUndefined();
    expect(sentSegments(instance)).toEqual([[undefined]]);
  });

  it("drops segments when the document changed while they were resolved", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const document = { ...FAKE_DOCUMENT, version: 1 } as TextDocument;
    const instance = makeSegmentClient(document);
    instance.resolveSegments.mockImplementation(async () => {
      (document as { version: number }).version = 2;
      return [segmentedHelp()];
    });

    await processDiagnostics(instance);

    expect(sentSegments(instance)).toEqual([[undefined]]);
  });

  it("drops segments when a newer pass supersedes this one", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    let resolveFirst!: (v: SegmentedDiagnostic[]) => void;
    instance.resolveSegments
      .mockReturnValueOnce(new Promise((resolve) => (resolveFirst = resolve)))
      .mockResolvedValueOnce([]);

    const first = processDiagnostics(instance);
    await processDiagnostics(instance);
    resolveFirst([segmentedHelp()]);
    await first;

    expect(sentSegments(instance)).toEqual([[undefined], [undefined]]);
  });

  it("carries segments over to the next pass, and removes them if they are gone", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValueOnce([segmentedHelp()]);
    await processDiagnostics(instance);

    // The next pass: the first message already has the segments...
    let resolveSecond!: (v: SegmentedDiagnostic[]) => void;
    instance.resolveSegments.mockReturnValueOnce(
      new Promise((resolve) => (resolveSecond = resolve)),
    );
    const second = processDiagnostics(instance);
    await new Promise((resolve) => setImmediate(resolve));
    expect(sentSegments(instance)[2]).toEqual([EXPECTED_SEGMENTS]);

    // ...and when the server no longer has them, they are sent without.
    resolveSecond([]);
    await second;
    expect(sentSegments(instance)[3]).toEqual([undefined]);
  });

  it("does not send the diagnostics again when the carried-over segments are unchanged", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    const instance = makeSegmentClient();
    instance.resolveSegments.mockResolvedValue([segmentedHelp()]);

    await processDiagnostics(instance);
    await processDiagnostics(instance);

    expect(sentSegments(instance)).toHaveLength(3);
  });

  it("does not carry segments over when the text they replace has changed", async () => {
    getDiagnostics.mockReturnValue([helpDiagnostic()]);
    let text = FAKE_TEXT;
    const document = { ...FAKE_DOCUMENT, getText: () => text } as TextDocument;
    const instance = makeSegmentClient(document);
    instance.resolveSegments.mockResolvedValueOnce([segmentedHelp()]);
    await processDiagnostics(instance);

    text = FAKE_TEXT.replace("line one", "LINE ONE");
    instance.resolveSegments.mockResolvedValueOnce(undefined);
    await processDiagnostics(instance);

    expect(sentSegments(instance)[2]).toEqual([undefined]);
  });
});
