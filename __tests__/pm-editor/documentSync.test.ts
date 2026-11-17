import {
  applyEdits,
  DEFAULT_QUIET_PERIOD_MS,
  DocumentSync,
  TextEdit,
} from "../../src/pm-editor/documentSync";
import { EditorDocumentSync } from "../../editor/src/documentSync";
import { Message, MessageType } from "../../shared";

/** Lets resolved promises run their callbacks. */
async function flush() {
  for (let i = 0; i < 10; i++) await Promise.resolve();
}

type ToExtensionHost =
  | { kind: "event"; text: string; version: number }
  | { kind: "reply"; ok: boolean; resolve: (ok: boolean) => void };

interface EditRequest {
  edits: TextEdit[];
  /** The document version the extension host knew when it sent the edit. */
  version: number;
  resolve: (ok: boolean) => void;
}

/**
 * A model of VS Code, the extension host and the editor webview, with the message channels
 * between them. Messages on each channel arrive in order, but the channels interleave freely.
 *
 * - VS Code holds the document. It refuses an edit when the document version differs from the
 *   version the extension host knew when it sent the edit, like `workspace.applyEdit`. Every
 *   change gives a new version, and is reported to the extension host before the reply to the
 *   edit that made it.
 * - The extension host has a copy of the document, updated by those reports.
 */
class World {
  main: { text: string; version: number };
  host: { text: string; version: number };
  toHost: ToExtensionHost[] = [];
  toMain: EditRequest[] = [];
  toEditor: Message[] = [];
  fromEditor: Message[] = [];

  editor!: { text: string; sync: EditorDocumentSync };
  sync: DocumentSync;

  inits = 0;
  discarded = 0;
  outsideEdits = 0;
  /** The text each change from the editor was made to, by its (unique) inserted text. */
  baseOf = new Map<string, string>();
  /** Edits from the editor that were sent to VS Code for text they were not made to. */
  violations: string[] = [];
  /** If set, VS Code changes the text of edits while applying them (like line endings). */
  normalize?: (text: string) => string;
  private tags = 0;

  constructor(text: string) {
    this.main = { text, version: 1 };
    this.host = { ...this.main };
    this.sync = new DocumentSync({
      documentText: () => this.host.text,
      documentVersion: () => this.host.version,
      applyEdits: (edits) => {
        this.checkBase(edits);
        return new Promise((resolve) =>
          this.toMain.push({ edits, version: this.host.version, resolve }),
        );
      },
      sendInit: (value, version, generation, webview) => {
        this.inits++;
        this.toEditor.push({
          type: MessageType.init,
          body: { value, version, generation, webview },
        });
      },
      reportDiscardedChanges: (count) => (this.discarded += count),
      editsFinished: () => {},
      log: (m) => process.env.SYNC_LOG && console.log(m),
    });
    this.newEditor();
  }

  /** The editor webview is (re)built: it shows nothing until its first `init`. */
  newEditor() {
    this.toEditor = [];
    this.editor = {
      text: "",
      sync: new EditorDocumentSync((msg) => this.fromEditor.push(msg)),
    };
    this.editor.sync.ready();
  }

  get shows() {
    return this.editor.text;
  }

  /** The user changes `[start, end)` in the editor. */
  type(start: number, end: number) {
    const text = `<${++this.tags}>`;
    this.baseOf.set(text, this.editor.text);
    this.editor.text = applyEdits(this.editor.text, [{ start, end, text }]);
    this.editor.sync.sendChange({
      startInFile: start,
      endInFile: end,
      finalText: text,
    });
  }

  /** Something else changes the document. */
  outsideEdit(start: number, end: number, text: string) {
    this.outsideEdits++;
    this.main.text = applyEdits(this.main.text, [{ start, end, text }]);
    this.main.version++;
    this.toHost.push({ kind: "event", ...this.main });
  }

  /** VS Code receives an edit from the extension. */
  deliverToMain() {
    const req = this.toMain.shift()!;
    if (req.version !== this.main.version) {
      this.toHost.push({ kind: "reply", ok: false, resolve: req.resolve });
      return;
    }
    const edits = this.normalize
      ? req.edits.map((e) => ({ ...e, text: this.normalize!(e.text) }))
      : req.edits;
    this.main.text = applyEdits(this.main.text, edits);
    this.main.version++;
    this.toHost.push({ kind: "event", ...this.main });
    this.toHost.push({ kind: "reply", ok: true, resolve: req.resolve });
  }

  async deliverToHost() {
    const msg = this.toHost.shift()!;
    if (msg.kind === "event") {
      this.host = { text: msg.text, version: msg.version };
      this.sync.documentChanged();
    } else {
      msg.resolve(msg.ok);
    }
    await flush();
  }

  deliverToEditor() {
    const msg = this.toEditor.shift()!;
    if (msg.type !== MessageType.init) return;
    if (this.editor.sync.acceptInit(msg.body))
      this.editor.text = msg.body.value;
  }

  async deliverFromEditor() {
    const msg = this.fromEditor.shift()!;
    if (msg.type === MessageType.ready) this.sync.editorReady(msg.body.webview);
    else if (msg.type === MessageType.docChange)
      this.sync.changeFromEditor(msg.body.change, msg.body.generation);
    await flush();
  }

  /** Delivers all messages and runs all timers, until nothing happens anymore. */
  async settle() {
    for (let i = 0; i < 1000; i++) {
      if (this.fromEditor.length) await this.deliverFromEditor();
      else if (this.toMain.length) this.deliverToMain();
      else if (this.toHost.length) await this.deliverToHost();
      else if (this.toEditor.length) this.deliverToEditor();
      else if (jest.getTimerCount() > 0) {
        jest.advanceTimersByTime(1000);
        await flush();
      } else {
        expect(this.violations).toEqual([]);
        return;
      }
    }
    throw new Error("did not settle");
  }

  /** Checks that an edit from the editor is applied to exactly the text it was made to. */
  private checkBase(edits: TextEdit[]) {
    if (edits.length !== 1) return;
    const base = this.baseOf.get(edits[0].text);
    if (base !== undefined && base !== this.host.text)
      this.violations.push(
        `edit ${edits[0].text} made to ${JSON.stringify(base)} applied to ${JSON.stringify(this.host.text)}`,
      );
  }
}

beforeEach(() => {
  jest.useFakeTimers();
});

afterEach(() => {
  jest.useRealTimers();
});

async function started(text = "hello world") {
  const w = new World(text);
  await w.settle();
  return w;
}

describe("DocumentSync", () => {
  it("sends the document when the editor is ready", async () => {
    const w = await started();
    expect(w.shows).toBe("hello world");
    expect(w.inits).toBe(1);
  });

  it("applies changes from the editor in order", async () => {
    const w = await started();
    w.type(0, 0);
    w.type(3, 4);
    w.type(w.shows.length, w.shows.length);
    await w.settle();
    expect(w.main.text).toBe(w.shows);
    expect(w.inits).toBe(1);
    expect(w.discarded).toBe(0);
  });

  it("resets the editor after an outside change, once the document is left alone", async () => {
    const w = await started();
    w.outsideEdit(0, 5, "HELLO");
    await w.deliverToHost();
    jest.advanceTimersByTime(DEFAULT_QUIET_PERIOD_MS - 1);
    w.outsideEdit(0, 0, "> ");
    await w.deliverToHost();
    jest.advanceTimersByTime(DEFAULT_QUIET_PERIOD_MS - 1);
    expect(w.toEditor).toHaveLength(0);
    jest.advanceTimersByTime(1);
    w.deliverToEditor();
    expect(w.shows).toBe("> HELLO world");
  });

  it("discards changes made before the reset, and reports them", async () => {
    const w = await started();
    w.outsideEdit(0, 0, "X");
    w.type(5, 5);
    await w.settle();
    expect(w.main.text).toBe("Xhello world");
    expect(w.shows).toBe("Xhello world");
    expect(w.discarded).toBe(1);
  });

  it("discards an edit VS Code refuses, and resets", async () => {
    const w = await started();
    w.type(0, 0);
    await w.deliverFromEditor(); // the extension sends the edit to VS Code
    w.outsideEdit(0, 0, "X"); // which gets an outside change first
    await w.settle();
    expect(w.main.text).toBe("Xhello world");
    expect(w.shows).toBe("Xhello world");
    expect(w.discarded).toBe(1);
  });

  it("resets when an outside change lands right after an edit", async () => {
    const w = await started();
    w.type(0, 0);
    await w.deliverFromEditor();
    w.deliverToMain();
    w.outsideEdit(0, 0, "X");
    await w.settle();
    expect(w.main.text).toBe("X<1>hello world");
    expect(w.shows).toBe(w.main.text);
    expect(w.discarded).toBe(0);
  });

  it("resets when VS Code changes the text of an edit", async () => {
    const w = await started();
    w.normalize = (t) => t.replace("<", "[");
    w.type(0, 0);
    await w.settle();
    expect(w.main.text).toBe("[1>hello world");
    expect(w.shows).toBe(w.main.text);
  });

  it("replaces the document, and then resets the editor", async () => {
    const w = await started();
    w.sync.replaceDocument("restored");
    await w.settle();
    expect(w.main.text).toBe("restored");
    expect(w.shows).toBe("restored");
  });

  it("applies queued changes before resetting a rebuilt editor", async () => {
    const w = await started();
    w.type(0, 0);
    w.type(0, 0);
    w.newEditor();
    await w.deliverFromEditor();
    await w.deliverFromEditor();
    await w.deliverFromEditor(); // ready, while the changes are queued
    jest.advanceTimersByTime(1000);
    await w.settle();
    expect(w.shows).toBe("<2><1>hello world");
    expect(w.discarded).toBe(0);
  });

  it("sends the document again to a rebuilt editor", async () => {
    const w = await started();
    w.type(0, 0);
    w.newEditor();
    await w.settle();
    expect(w.shows).toBe("<1>hello world");
    expect(w.main.text).toBe(w.shows);
    expect(w.discarded).toBe(0);
  });
});

function mulberry32(seed: number) {
  return () => {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/**
 * Runs `steps` random steps: the user types in the editor, something else changes the document
 * (if `outside`), the webview is rebuilt, messages are delivered, time passes. Every edit from
 * the editor is checked to apply to exactly the text it was made to.
 */
async function randomRun(seed: number, outside: boolean, steps = 150) {
  const rand = mulberry32(seed);
  const int = (n: number) => Math.floor(rand() * n);
  const range = (len: number) => {
    const a = int(len + 1);
    return [a, Math.min(len, a + int(3))] as const;
  };
  const w = new World("The quick brown fox.\n");
  for (let i = 0; i < steps; i++) {
    const r = rand();
    if (r < 0.25) {
      if (w.shows !== "") w.type(...range(w.shows.length));
    } else if (r < 0.32) {
      if (outside) w.outsideEdit(...range(w.main.text.length), "#");
    } else if (r < 0.34) {
      w.newEditor();
    } else if (r < 0.48) {
      if (w.fromEditor.length) await w.deliverFromEditor();
    } else if (r < 0.62) {
      if (w.toMain.length) w.deliverToMain();
    } else if (r < 0.76) {
      if (w.toHost.length) await w.deliverToHost();
    } else if (r < 0.88) {
      if (w.toEditor.length) w.deliverToEditor();
    } else {
      jest.advanceTimersByTime(int(2 * DEFAULT_QUIET_PERIOD_MS));
      await flush();
    }
  }
  await w.settle();
  return w;
}

const SEEDS = Array.from({ length: 200 }, (_, i) => i + 1);

describe("DocumentSync, random runs", () => {
  it.each(SEEDS)(
    "the editor shows the document in the end, with outside changes (seed %i)",
    async (seed) => {
      const w = await randomRun(seed, true);
      expect(w.shows).toBe(w.main.text);
      expect(w.host).toEqual(w.main);
    },
  );

  it.each(SEEDS)(
    "nothing is discarded when only the editor changes the document (seed %i)",
    async (seed) => {
      const w = await randomRun(seed, false);
      expect(w.shows).toBe(w.main.text);
      expect(w.discarded).toBe(0);
    },
  );
});
