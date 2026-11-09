import {
  afterEach,
  beforeEach,
  describe,
  expect,
  it,
  jest,
} from "@jest/globals";

// Tests for how WaterproofWebview refreshes the editor after the document is saved.

// Settings in the `files` section, as returned by the mocked `workspace.getConfiguration`.
let settings: Record<string, boolean> = {};

jest.mock(
  "vscode",
  () => {
    class Range {
      constructor(
        public start: unknown,
        public end: unknown,
      ) {}
    }
    class WorkspaceEdit {
      insert = jest.fn();
      delete = jest.fn();
      replace = jest.fn();
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
          get: (key: string, def?: unknown) => settings[key] ?? def,
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

const uri = {
  fsPath: "/doc.mv",
  toString: () => "file:///doc.mv",
};

/** A fake text document whose text and version change when workspace edits are applied. */
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
let save: Handler;
/** Resolvers of the `workspace.applyEdit` calls that are still in progress. */
let pendingEdits: Array<() => void>;

/** Lets the promise callbacks of resolved edits run. */
async function flush() {
  for (let i = 0; i < 5; i++) await Promise.resolve();
}

/** Completes the oldest in-progress workspace edit, deleting one character from the document. */
async function completeEdit() {
  pendingEdits.shift()!();
  await flush();
}

function sendDeletionFromEditor(at: number) {
  receiveMessage({
    type: MessageType.docChange,
    body: { startInFile: at, endInFile: at + 1, finalText: "" },
  });
}

function refreshMessages() {
  return postMessage.mock.calls
    .map(([msg]) => msg as { type: MessageType; body: unknown })
    .filter((msg) => msg.type === MessageType.refreshDocument);
}

beforeEach(async () => {
  jest.useFakeTimers();
  settings = {};
  pendingEdits = [];
  doc = makeDocument("abcdef");

  jest.mocked(vscode.workspace.applyEdit).mockImplementation(
    () =>
      new Promise<boolean>((resolve) => {
        pendingEdits.push(() => {
          doc.text = doc.text.slice(0, -1);
          doc.version++;
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

  const saveListeners = jest.mocked(vscode.workspace.onDidSaveTextDocument).mock
    .calls;
  save = saveListeners[saveListeners.length - 1][0] as Handler;
  postMessage.mockClear();
});

afterEach(() => {
  jest.clearAllTimers();
  jest.useRealTimers();
  jest.clearAllMocks();
});

describe("refresh after saving", () => {
  it("does not refresh when no setting changes the text on save", () => {
    save(doc);
    expect(refreshMessages()).toHaveLength(0);
  });

  it.each([
    "trimTrailingWhitespace",
    "trimFinalNewlines",
    "insertFinalNewline",
  ])("refreshes when files.%s is enabled", (setting) => {
    settings = { [setting]: true };
    save(doc);
    expect(refreshMessages()).toEqual([
      {
        type: MessageType.refreshDocument,
        body: { value: "abcdef", version: 1 },
      },
    ]);
  });

  it("ignores saves of other documents", () => {
    settings = { trimTrailingWhitespace: true };
    save({ uri: { toString: () => "file:///other.mv" } });
    expect(refreshMessages()).toHaveLength(0);
  });

  it("waits until queued edits from the editor are applied", async () => {
    settings = { trimTrailingWhitespace: true };
    sendDeletionFromEditor(5);
    sendDeletionFromEditor(4);

    save(doc);
    expect(refreshMessages()).toHaveLength(0);

    await completeEdit();
    expect(refreshMessages()).toHaveLength(0);

    await completeEdit();
    expect(refreshMessages()).toEqual([
      {
        type: MessageType.refreshDocument,
        body: { value: "abcd", version: 3 },
      },
    ]);
  });

  it("sends a single refresh for several saves during queued edits", async () => {
    settings = { trimTrailingWhitespace: true };
    sendDeletionFromEditor(5);
    save(doc);
    save(doc);

    await completeEdit();
    expect(refreshMessages()).toHaveLength(1);
  });

  it("does not refresh after queued edits when there was no save", async () => {
    settings = { trimTrailingWhitespace: true };
    sendDeletionFromEditor(5);

    await completeEdit();
    expect(refreshMessages()).toHaveLength(0);
  });
});
