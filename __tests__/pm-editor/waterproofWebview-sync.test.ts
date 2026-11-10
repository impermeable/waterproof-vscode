// NOTE: These tests were AI-generated. They describe the current behaviour of the code and
// may therefore codify existing buggy behaviour; a failing test is not necessarily a regression.

import {
  afterEach,
  beforeEach,
  describe,
  expect,
  it,
  jest,
} from "@jest/globals";

// Tests for how WaterproofWebview keeps the editor and the document in sync.

jest.mock(
  "vscode",
  () => {
    class Range {
      constructor(
        public start: number,
        public end: number,
      ) {}
    }
    /** Records its edits as offsets (positions are offsets in the fake document). */
    class WorkspaceEdit {
      edits: Array<{ from: number; to: number; text: string }> = [];
      insert(_uri: unknown, pos: number, text: string) {
        this.edits.push({ from: pos, to: pos, text });
      }
      delete(_uri: unknown, range: Range) {
        this.edits.push({ from: range.start, to: range.end, text: "" });
      }
      replace(_uri: unknown, range: Range, text: string) {
        this.edits.push({ from: range.start, to: range.end, text });
      }
    }
    const listener = () => jest.fn(() => ({ dispose: jest.fn() }));
    return {
      Range,
      WorkspaceEdit,
      EndOfLine: { LF: 1, CRLF: 2 },
      ColorThemeKind: { Light: 1, Dark: 2, HighContrast: 3 },
      Uri: { joinPath: jest.fn(() => ({})) },
      window: {
        activeColorTheme: { kind: 2 },
        onDidChangeActiveColorTheme: listener(),
        showWarningMessage: jest.fn(() => Promise.resolve(undefined)),
        showErrorMessage: jest.fn(() => Promise.resolve(undefined)),
      },
      workspace: {
        getConfiguration: jest.fn(() => ({
          get: (_key: string, def?: unknown) => def,
        })),
        applyEdit: jest.fn(),
        onDidSaveTextDocument: listener(),
        onDidChangeTextDocument: listener(),
        onDidChangeConfiguration: listener(),
      },
      commands: { executeCommand: jest.fn() },
      extensions: { getExtension: jest.fn(), all: [] },
      env: {},
    };
  },
  { virtual: true },
);

jest.mock("../../src/helpers", () => ({
  WaterproofConfigHelper: { get: jest.fn(() => false) },
  WaterproofFileUtil: { getBasename: jest.fn(() => "doc.mv") },
  WaterproofLogger: { log: jest.fn(), debug: jest.fn() },
  WaterproofSetting: {},
  qualifiedSettingName: jest.fn((s: string) => s),
}));

// Avoid loading the editor provider (and through it the webview manager).
jest.mock("../../src/pm-editor/waterproofEditor", () => ({}));

import * as vscode from "vscode";
import { MessageType } from "../../shared";
import { WaterproofWebview } from "../../src/pm-editor/waterproofWebview";

type Handler = (arg: unknown) => void;
type RecordedEdit = { from: number; to: number; text: string };

const uri = {
  fsPath: "/doc.mv",
  toString: () => "file:///doc.mv",
};

/** A fake text document; positions are plain offsets. */
function makeDocument(text: string) {
  return {
    uri,
    languageId: "rocq",
    eol: vscode.EndOfLine.LF,
    version: 1,
    text,
    getText() {
      return this.text;
    },
    positionAt: (offset: number) => offset,
  };
}

let doc: ReturnType<typeof makeDocument>;
let postMessage: jest.Mock;
let receiveMessage: Handler;
let documentChanged: Handler;
/** Completers of the `workspace.applyEdit` calls that are still in progress. */
let pendingEdits: Array<() => void>;

/** Lets the promise callbacks of resolved edits run. */
async function flush() {
  for (let i = 0; i < 5; i++) await Promise.resolve();
}

/** Changes the document text and notifies the listeners, as VS Code does. */
function changeDocument(edits: RecordedEdit[]) {
  for (const e of [...edits].sort((a, b) => b.from - a.from))
    doc.text = doc.text.slice(0, e.from) + e.text + doc.text.slice(e.to);
  doc.version++;
  documentChanged({ document: doc });
}

/** Completes the oldest in-progress workspace edit. */
async function completeEdit() {
  pendingEdits.shift()!();
  await flush();
}

async function completeAllEdits() {
  while (pendingEdits.length) await completeEdit();
}

function sendChange(startInFile: number, endInFile: number, finalText: string) {
  receiveMessage({
    type: MessageType.docChange,
    body: { startInFile, endInFile, finalText },
  });
}

function sendRefreshResult(accepted: boolean) {
  receiveMessage({ type: MessageType.refreshResult, body: { accepted } });
}

function refreshMessages() {
  return postMessage.mock.calls
    .map(([msg]) => msg as { type: MessageType; body: unknown })
    .filter((msg) => msg.type === MessageType.refreshDocument)
    .map((msg) => msg.body);
}

beforeEach(async () => {
  jest.useFakeTimers();
  pendingEdits = [];
  doc = makeDocument("abcdef");

  jest.mocked(vscode.workspace.applyEdit).mockImplementation(
    (edit) =>
      new Promise<boolean>((resolve) => {
        pendingEdits.push(() => {
          const edits = (edit as unknown as { edits: RecordedEdit[] }).edits;
          if (edits.length) changeDocument(edits);
          resolve(true);
        });
      }),
  );

  postMessage = jest.fn();
  const panel = {
    webview: {
      options: {},
      html: "",
      asWebviewUri: jest.fn(() => "uri"),
      postMessage,
      onDidReceiveMessage: jest.fn((handler: Handler) => {
        receiveMessage = handler;
        return { dispose: jest.fn() };
      }),
    },
    onDidDispose: jest.fn(),
    onDidChangeViewState: jest.fn(),
    dispose: jest.fn(),
  };
  const provider = {
    disposeHistoryCommandListeners: jest.fn(),
    registerHistoryCommandListeners: jest.fn(),
  };

  await WaterproofWebview.createWaterproofView(
    panel as never,
    {} as never,
    doc as never,
    provider as never,
  );

  const changeListeners = jest.mocked(vscode.workspace.onDidChangeTextDocument)
    .mock.calls;
  documentChanged = changeListeners[changeListeners.length - 1][0] as Handler;
  postMessage.mockClear();
});

afterEach(() => {
  jest.clearAllTimers();
  jest.useRealTimers();
  jest.clearAllMocks();
});

describe("changes from the editor", () => {
  it("are applied at their offsets", async () => {
    sendChange(1, 2, "X");
    sendChange(5, 6, "");
    await completeAllEdits();

    expect(doc.text).toBe("aXcde");
    expect(refreshMessages()).toHaveLength(0);
  });

  it("are moved past changes made to the document in the meantime", async () => {
    changeDocument([{ from: 0, to: 0, text: "XY" }]);
    // The editor did not see that change yet.
    sendChange(5, 6, "");
    await completeAllEdits();

    expect(doc.text).toBe("XYabcde");
  });

  it("are dropped when they conflict with a change to the document", async () => {
    changeDocument([{ from: 2, to: 4, text: "Z" }]);
    sendChange(3, 4, "");
    await completeAllEdits();

    expect(doc.text).toBe("abZef");
  });
});

describe("refreshing the editor", () => {
  it("happens when the document is changed outside the editor", () => {
    changeDocument([{ from: 0, to: 0, text: "X" }]);

    expect(refreshMessages()).toEqual([
      { value: "Xabcdef", version: 2, receivedChanges: 0 },
    ]);
  });

  it("waits until queued edits from the editor are applied", async () => {
    sendChange(5, 6, "");
    sendChange(4, 5, "");
    changeDocument([{ from: 6, to: 6, text: "X" }]);
    expect(refreshMessages()).toHaveLength(0);

    await completeEdit();
    expect(refreshMessages()).toHaveLength(0);

    await completeEdit();
    expect(refreshMessages()).toEqual([
      { value: "abcdX", version: 4, receivedChanges: 2 },
    ]);
  });

  it("sends one refresh at a time, and the latest text after an answer", () => {
    changeDocument([{ from: 0, to: 0, text: "X" }]);
    changeDocument([{ from: 0, to: 0, text: "Y" }]);
    expect(refreshMessages()).toHaveLength(1);

    sendRefreshResult(true);
    expect(refreshMessages()).toEqual([
      { value: "Xabcdef", version: 2, receivedChanges: 0 },
      { value: "YXabcdef", version: 3, receivedChanges: 0 },
    ]);
  });

  it("stops once the editor accepted the current text", async () => {
    changeDocument([{ from: 0, to: 0, text: "X" }]);
    sendRefreshResult(true);

    // The editor now bases its changes on the refreshed text.
    sendChange(7, 7, "!");
    await completeAllEdits();

    expect(doc.text).toBe("Xabcdef!");
    expect(refreshMessages()).toHaveLength(1);
  });

  it("is repeated, including the late changes, when the editor rejected it", async () => {
    changeDocument([{ from: 0, to: 0, text: "X" }]);
    // The editor had already sent a change when the refresh arrived, and rejects it.
    sendChange(5, 6, "");
    sendRefreshResult(false);
    expect(refreshMessages()).toHaveLength(1);

    await completeAllEdits();
    expect(refreshMessages()).toEqual([
      { value: "Xabcdef", version: 2, receivedChanges: 0 },
      { value: "Xabcde", version: 3, receivedChanges: 1 },
    ]);
  });

  it("brings back the document text after a conflicting change was dropped", async () => {
    changeDocument([{ from: 2, to: 4, text: "Z" }]);
    sendChange(3, 4, "");
    sendRefreshResult(false);
    await completeAllEdits();

    expect(refreshMessages()).toEqual([
      { value: "abZef", version: 2, receivedChanges: 0 },
      { value: "abZef", version: 2, receivedChanges: 1 },
    ]);
  });
});
