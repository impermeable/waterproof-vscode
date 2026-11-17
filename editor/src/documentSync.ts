import type {
  DocChange,
  WrappingDocChange,
} from "@impermeable/waterproof-editor";
import { Message, MessageType } from "../../shared";

/** A random id for this instance of the webview. */
function newWebviewId(): string {
  return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;
}

/**
 * The editor's side of keeping the editor and the document in the extension in sync (see
 * `src/pm-editor/documentSync.ts`): the editor tags each change it sends with the generation of
 * the content it shows, from the last `init`. The extension discards changes made to content it
 * has since replaced.
 *
 * VS Code rebuilds the webview when it is hidden and shown again. `ready` carries an id of the
 * webview instance, and `init` is addressed to one: content meant for an earlier instance is
 * ignored, as the extension replaces it right away.
 */
export class EditorDocumentSync {
  /** The generation of the content the editor shows; 0 before the first `init`. */
  private generation = 0;

  constructor(
    private readonly post: (msg: Message) => void,
    readonly webview: string = newWebviewId(),
  ) {}

  /** Tells the extension that this webview has loaded. */
  ready(): void {
    this.post({ type: MessageType.ready, body: { webview: this.webview } });
  }

  /**
   * Handles `init`.
   * @returns Whether the editor should show the content.
   */
  acceptInit(body: { generation: number; webview: string }): boolean {
    if (body.webview !== this.webview) return false;
    this.generation = body.generation;
    return true;
  }

  /** Sends a change made in the editor to the extension. */
  sendChange(change: DocChange | WrappingDocChange): void {
    this.post({
      type: MessageType.docChange,
      body: { change, generation: this.generation },
    });
  }
}
