import type {
  DocChange,
  WrappingDocChange,
} from "@impermeable/waterproof-editor";

/**
 * Keeps the Waterproof editor (the webview) and the text document in sync.
 *
 * The editor is the only one that changes the document while it is in sync. It sends its
 * changes in order, each tagged with the generation of the content it was made to. A change is
 * applied only to exactly the text it was made to: the document must still be at the version
 * the editor's content corresponds to. VS Code enforces the same for the edit itself (it refuses
 * an edit when the document changed after the edit was sent), so an edit never lands on text it
 * was not made for.
 *
 * Whenever the document is changed by anything else (a text editor, save actions, other
 * extensions, undo in a text editor), or anything unexpected happens, the editor is reset: it
 * gets the document's text with a new generation, and changes still on their way from the
 * editor, made to the old content, are discarded. Every doubt leads to a reset, never to a guess.
 *
 * This class does not depend on VS Code; see {@linkcode DocumentSyncHost}.
 */

export type EditorChange = DocChange | WrappingDocChange;

/** A change to a text: replace `[start, end)` with `text`. */
export interface TextEdit {
  start: number;
  end: number;
  text: string;
}

export interface DocumentSyncHost {
  /** The current text of the document. */
  documentText(): string;
  /** The current version of the document. */
  documentVersion(): number;
  /**
   * Applies `edits` (offsets into the current document) as one edit. Must send the edit to VS
   * Code synchronously, so that the version check made just before still holds.
   * @returns Whether the edit was applied.
   */
  applyEdits(edits: TextEdit[]): PromiseLike<boolean>;
  /** Sends `init` to the editor webview with id `webview`. */
  sendInit(
    text: string,
    version: number,
    generation: number,
    webview: string,
  ): void;
  /** Tells the user that changes made in the editor were discarded. */
  reportDiscardedChanges(count: number): void;
  /** Called when all queued edits have been applied. */
  editsFinished(): void;
  log(message: string): void;
}

/** How long the document must be left alone before the editor is reset, in milliseconds. */
export const DEFAULT_QUIET_PERIOD_MS = 300;

/** How long to collect discarded changes before telling the user, in milliseconds. */
const REPORT_DELAY_MS = 500;

/** The edits of `change`, each expressed in offsets into the text the change is based on. */
export function editsOf(change: EditorChange): TextEdit[] {
  const edits =
    "firstEdit" in change ? [change.firstEdit, change.secondEdit] : [change];
  return edits.map((e) => ({
    start: e.startInFile,
    end: e.endInFile,
    text: e.finalText,
  }));
}

/** Applies edits that are all expressed in offsets into `text`. */
export function applyEdits(text: string, edits: TextEdit[]): string {
  // Apply them from the back, so that applying one does not shift the others.
  return [...edits]
    .sort((a, b) => b.start - a.start)
    .reduce(
      (acc, e) => acc.slice(0, e.start) + e.text + acc.slice(e.end),
      text,
    );
}

type QueuedEdit =
  | { kind: "editor"; edits: TextEdit[]; generation: number }
  | { kind: "replace"; text: string };

export class DocumentSync {
  /** Counts resets; the editor tags its changes with the generation of its content. */
  private generation = 0;

  /** The document version the editor's content corresponds to (with the applied changes). */
  private version = -1;

  /** The text of the document at {@linkcode version}. */
  private text = "";

  /** The text the editor shows: {@linkcode text} with the queued changes applied. */
  private editorText = "";

  /** The id of the webview instance that sent the last `ready`. */
  private webview = "";

  private readonly queue: QueuedEdit[] = [];

  /** Whether an edit is being applied. */
  private applying = false;

  /** Whether the editor must be reset, once no edit is being applied. */
  private resetNeeded = false;

  private resetTimer?: ReturnType<typeof setTimeout>;

  private discarded = 0;
  private reportTimer?: ReturnType<typeof setTimeout>;

  constructor(
    private readonly host: DocumentSyncHost,
    private readonly quietPeriodMs = DEFAULT_QUIET_PERIOD_MS,
  ) {}

  /** Whether edits are queued or being applied. */
  get editsInProgress(): boolean {
    return this.applying || this.queue.length > 0;
  }

  /** The editor webview with id `webview` has (re)loaded, and needs the document. */
  editorReady(webview: string): void {
    this.webview = webview;
    this.requestReset(0);
  }

  /**
   * Handles a change from the editor, made to the content of `generation`.
   * @returns The text the editor shows after the change, or `undefined` if it was discarded.
   */
  changeFromEditor(
    change: EditorChange,
    generation: number,
  ): string | undefined {
    if (generation !== this.generation) {
      // Made to content that has since been replaced.
      this.discard("made to replaced content");
      return undefined;
    }
    const edits = editsOf(change);
    this.editorText = applyEdits(this.editorText, edits);
    this.queue.push({ kind: "editor", edits, generation });
    this.next();
    return this.editorText;
  }

  /** The document changed: by one of the queued edits, or by something else. */
  documentChanged(): void {
    // An edit being applied is checked when it is done; before the first reset there is
    // nothing to compare with.
    if (this.applying || this.generation === 0) return;
    if (this.host.documentVersion() !== this.version)
      this.requestReset(this.quietPeriodMs);
  }

  /** Replaces the whole document with `text`, and then resets the editor. */
  replaceDocument(text: string): void {
    this.queue.push({ kind: "replace", text });
    this.next();
  }

  dispose(): void {
    clearTimeout(this.resetTimer);
    clearTimeout(this.reportTimer);
  }

  /** Resets the editor once the document has been left alone for `delay` milliseconds. */
  private requestReset(delay: number): void {
    this.resetNeeded = true;
    clearTimeout(this.resetTimer);
    this.resetTimer = setTimeout(() => {
      this.resetTimer = undefined;
      this.resetIfIdle();
    }, delay);
  }

  /** Resets the editor if one is needed, the quiet period is over, and no edits are queued. */
  private resetIfIdle(): void {
    // Changes from the editor that are still queued are applied first if they can be (after a
    // rebuild of the webview), or discarded (after an outside change).
    if (
      !this.resetNeeded ||
      this.resetTimer !== undefined ||
      this.editsInProgress
    )
      return;
    this.resetNeeded = false;
    this.generation++;
    this.version = this.host.documentVersion();
    this.text = this.host.documentText();
    this.editorText = this.text;
    this.host.sendInit(this.text, this.version, this.generation, this.webview);
    this.host.editsFinished();
  }

  /** Applies the next queued edit, if no edit is being applied. */
  private next(): void {
    if (this.applying) return;
    const queued = this.queue.shift();
    if (queued === undefined) {
      if (this.resetNeeded) this.resetIfIdle();
      else this.host.editsFinished();
      return;
    }

    if (queued.kind === "replace") {
      const current = this.host.documentText();
      this.apply([{ start: 0, end: current.length, text: queued.text }], () =>
        this.requestReset(0),
      );
      return;
    }

    if (
      queued.generation !== this.generation ||
      this.host.documentVersion() !== this.version
    ) {
      // The document is not the text the change was made to.
      this.discard("made to outdated text");
      if (!this.resetNeeded) this.requestReset(this.quietPeriodMs);
      this.next();
      return;
    }

    const expected = applyEdits(this.text, queued.edits);
    const before = this.version;
    this.apply(queued.edits, (ok) => {
      if (!ok) {
        // VS Code refused it: the document changed after the check above.
        this.discard("refused by VS Code");
        this.requestReset(this.quietPeriodMs);
      } else if (
        this.host.documentVersion() === before + 1 &&
        this.host.documentText() === expected
      ) {
        this.version = before + 1;
        this.text = expected;
      } else {
        // Applied, but something else changed the document too, or VS Code changed the text
        // while applying it (e.g. line endings).
        this.requestReset(this.quietPeriodMs);
      }
    });
  }

  /** Applies `edits`; then calls `done` with whether they were applied, and continues. */
  private apply(edits: TextEdit[], done: (ok: boolean) => void): void {
    this.applying = true;
    let result: PromiseLike<boolean>;
    try {
      result = this.host.applyEdits(edits);
    } catch (e) {
      result = Promise.reject(e);
    }
    Promise.resolve(result).then(
      (ok) => this.finish(done, ok),
      (reason) => {
        this.host.log(`[sync] Edit failed: ${reason}`);
        this.finish(done, false);
      },
    );
  }

  private finish(done: (ok: boolean) => void, ok: boolean): void {
    this.applying = false;
    done(ok);
    this.next();
  }

  /** Discards a change from the editor, and tells the user (once for a burst of them). */
  private discard(why: string): void {
    this.host.log(`[sync] Discarded a change from the editor: ${why}`);
    this.discarded++;
    if (this.reportTimer !== undefined) return;
    this.reportTimer = setTimeout(() => {
      this.reportTimer = undefined;
      this.host.reportDiscardedChanges(this.discarded);
      this.discarded = 0;
    }, REPORT_DELAY_MS);
  }
}
