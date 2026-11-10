import type { MessageHandlerEditor } from "@impermeable/waterproof-editor";
import { Message, MessageType, ServerStatus } from "../../shared";

/** The editor operations used by the message handler. */
export type HandledEditor = MessageHandlerEditor & {
  serializeDocument?: () => string | undefined;
};

/** State the editor keeps to stay in sync with the document in the extension. */
export interface DocumentSync {
  /** The number of changes sent to the extension since the editor was initialized. */
  sentChanges: number;
  /** Sends a message to the extension. */
  reply: (msg: Message) => void;
}

/**
 * Replaces the content of the editor. `refreshDocument` skips the update when `version` equals
 * the editor's own version, which can happen while the content differs (e.g. when the extension
 * dropped a change that conflicted with a change to the document); force the update then.
 */
function refreshDocument(
  editor: HandledEditor,
  value: string,
  version: number,
) {
  editor.refreshDocument(value, version);
  if (
    editor.serializeDocument !== undefined &&
    editor.serializeDocument() !== value
  ) {
    editor.refreshDocument(value, Number.NaN);
    editor.refreshDocument(value, version);
  }
}

export function handleEditorMessage(
  editor: HandledEditor,
  msg: Message,
  sync?: DocumentSync,
): void {
  switch (msg.type) {
    case MessageType.init:
      // The extension starts counting the changes it receives anew.
      if (sync) sync.sentChanges = 0;
      editor.init(msg.body.value, msg.body.version);
      break;
    case MessageType.insert: {
      // Insert symbol message, retrieve the symbol from the message.
      const { symbolUnicode } = msg.body;
      if (msg.body.type === "tactics") {
        // `symbolUnicode` stores the tactic template.
        if (!symbolUnicode) {
          console.error("no template provided for snippet");
          return;
        }
        editor.handleSnippet(symbolUnicode);
      } else {
        editor.insertSymbol(symbolUnicode);
      }
      break;
    }
    case MessageType.refreshDocument: {
      // A refresh that misses changes this editor has sent would undo them; reject it. The
      // extension sends a new refresh once it has applied those changes.
      const accepted =
        sync === undefined || msg.body.receivedChanges === sync.sentChanges;
      if (accepted) refreshDocument(editor, msg.body.value, msg.body.version);
      sync?.reply({ type: MessageType.refreshResult, body: { accepted } });
      break;
    }
    case MessageType.replaceRange: {
      const { start, end, text } = msg.body;
      editor.replaceRange(start, end, text);
      break;
    }
    case MessageType.setAutocomplete:
      // Handle autocompletion
      editor.handleCompletions(msg.body);
      break;
    case MessageType.qedStatus: {
      const statuses = msg.body; // one status for each input area, in order
      editor.setInputAreaStatus(statuses);
      break;
    }
    case MessageType.setShowLineNumbers: {
      const show = msg.body;
      editor.setShowLineNumbers(show);
      break;
    }
    case MessageType.setShowMenuItems: {
      const show = msg.body;
      editor.setShowMenuItems(show);
      break;
    }
    case MessageType.editorHistoryChange:
      editor.handleHistoryChange(msg.body);
      break;
    case MessageType.teacher:
      editor.setTeacherMode(msg.body);
      break;
    case MessageType.progress: {
      const { numberOfLines, progress } = msg.body;
      if (progress.length === 0) {
        editor.removeBusyIndicators();
        editor.reportProgress(numberOfLines, numberOfLines, "File verified");
      } else {
        const at = progress[0].range.start.line + 1;
        editor.reportProgress(
          at,
          numberOfLines,
          `Verified file up to line: ${at}`,
        );
      }
      break;
    }
    case MessageType.executionInfo: {
      const range = msg.body;
      editor.setBusyIndicator(range.from);
      break;
    }
    case MessageType.diagnostics:
      editor.setActiveDiagnostics(
        msg.body.positionedDiagnostics,
        msg.body.version,
      );
      break;
    case MessageType.serverStatus: {
      const status: ServerStatus = msg.body;
      if (status.status === "Busy") {
        editor.startSpinner();
      } else {
        editor.stopSpinner();
      }
      break;
    }
    case MessageType.themeUpdate:
      editor.updateNodeViewThemes(msg.body.theme);
      break;
    default:
      // If we reach this 'default' case, then we have encountered an unknown message type.
      console.log(`[WEBVIEW] Unrecognized message type '${msg.type}'`);
      break;
  }
}
