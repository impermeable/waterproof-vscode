import { EventEmitter } from "events";
import {
  ColorThemeKind,
  Disposable,
  EndOfLine,
  Range,
  TextDocument,
  Uri,
  WebviewPanel,
  WorkspaceEdit,
  commands,
  window,
  workspace,
} from "vscode";

import { checkTextChangingSaveSettings, getNonce } from "../util";
import { WebviewEvents, WebviewState } from "../webviews/waterproofPanel";
import { SequentialEditor } from "./edit";
import { applyDocChange, mapDocChange } from "./documentSync";
import { getFormatFromExtension, isIllegalFileName } from "./fileUtils";

const SAVE_AS = "Save As";
import {
  qualifiedSettingName,
  WaterproofConfigHelper,
  WaterproofFileUtil,
  WaterproofLogger,
  WaterproofSetting,
} from "../helpers";
import { getNonInputRegions, showRestoreMessage } from "./file-utils";
import { WaterproofEditorProvider } from "./waterproofEditor";
import { FileFormat, Message, MessageType } from "../../shared";
import {
  DocChange,
  HistoryChange,
  ThemeStyle,
  WrappingDocChange,
} from "@impermeable/waterproof-editor";

/** How long to wait for the editor webview to report itself ready. */
const READY_TIMEOUT_MS = 10_000;

export class WaterproofWebview extends EventEmitter {
  /** The webview panel of this ProseMirror instance */
  private _panel: WebviewPanel;

  /** The document associated with this ProseMirror instance */
  private readonly _document: TextDocument;

  /** The file format of the doc associated with this ProseMirror instance */
  private readonly _format: FileFormat = FileFormat.MarkdownV;

  /** The editor that appends changes to the document associated with this panel */
  private readonly _workspaceEditor = new SequentialEditor();

  /** Disposables */
  private readonly _disposables: Disposable[] = [];

  private _teacherMode: boolean;
  private _enforceCorrectNonInputArea: boolean;
  private _lastCorrectDocString: string;

  private _provider: WaterproofEditorProvider;

  private _showLineNrsInEditor: boolean = WaterproofConfigHelper.get(
    WaterproofSetting.ShowLineNumbersInEditor,
  );
  private _showMenuItemsInEditor: boolean = WaterproofConfigHelper.get(
    WaterproofSetting.ShowMenuItemsInEditor,
  );

  /** These regions contain the strings that are outside of the <input-area> tags, but including the tags themselves */
  private _nonInputRegions: {
    to: number;
    from: number;
    content: string;
  }[];

  /**
   * Collection of messages that were sent before, and should be resent if the editor
   * reinitializes (because the LSP server does not re-emit them if the document did not change).
   * Whether a message should be cached is specified in the `postMessage` method. Only one message
   * per type is cached.
   */
  private _cachedMessages: Map<MessageType, Message>;

  /**
   * The text shown by the editor, as far as the extension knows: the text last sent to the
   * editor (and accepted by it), with all changes received from the editor since applied to it.
   * Whenever no edits are queued and this differs from the document, the editor is refreshed.
   */
  private _editorText: string;

  /**
   * The number of changes received from the editor since it was initialized. The editor counts
   * the changes it sends in the same way, and only accepts a refresh that includes all of them;
   * otherwise the refresh would undo its changes that are still on their way to the extension.
   */
  private _receivedChanges = 0;

  /** The text of the refresh that was sent to the editor and not yet accepted or rejected. */
  private _pendingRefresh?: string;

  /**
   * Watchdog for the editor bundle: the webview only renders once it has sent
   * `MessageType.ready`, at which point we answer with the document contents. If
   * `editor_output/index.js` fails to load or throws while evaluating, that
   * message never arrives and the editor stays blank with no error on the
   * extension side, so time it out and say so.
   */
  private _readyTimeout?: ReturnType<typeof setTimeout>;

  /** Checks whether the document is currently being changed */
  get documentIsUpToDate() {
    return !this._workspaceEditor.isInProgress;
  }

  // Handlers for undo and redo actions.
  // These can either be triggered by the user via a keybinding or by the undo/redo command
  //     under `edit > edit` and `edit > undo` in the menubar.
  private undoHandler() {
    this.sendHistoryChangeToEditor(HistoryChange.Undo);
  }
  private redoHandler() {
    this.sendHistoryChangeToEditor(HistoryChange.Redo);
  }

  private constructor(
    webviewPanel: WebviewPanel,
    extensionUri: Uri,
    doc: TextDocument,
    provider: WaterproofEditorProvider,
  ) {
    super();

    this._provider = provider;
    this._provider.disposeHistoryCommandListeners(this);
    this._provider.registerHistoryCommandListeners(
      this,
      this.undoHandler.bind(this),
      this.redoHandler.bind(this),
    );

    const fileName = WaterproofFileUtil.getBasename(doc.uri);

    if (isIllegalFileName(fileName)) {
      const error = `The file "${fileName}" cannot be opened, most likely because it either contains a space " ", or one of the characters: "-", "(", ")". Please rename the file.`;
      window
        .showErrorMessage(error, { modal: true }, SAVE_AS)
        .then(this.handleFileNameSaveAs);
      WaterproofLogger.log("Error: Illegal file name encountered.");
    }

    this._panel = webviewPanel;
    this._workspaceEditor.onFinish(() => {
      this.refreshIfOutOfSync();
      this.emit(WebviewEvents.finishUpdate);
    });
    this._cachedMessages = new Map();
    this._document = doc;

    this._nonInputRegions = getNonInputRegions(doc.getText());

    this._teacherMode = WaterproofConfigHelper.get(
      WaterproofSetting.TeacherMode,
    );
    this._enforceCorrectNonInputArea = WaterproofConfigHelper.get(
      WaterproofSetting.EnforceCorrectNonInputArea,
    );
    this._lastCorrectDocString = doc.getText();
    this._editorText = doc.getText();
    checkTextChangingSaveSettings(doc);

    const format = getFormatFromExtension(doc);
    if (format === undefined) {
      // FIXME: We should never encounter this, as the extension is only activated for .v and .mv files?
      WaterproofLogger.log(
        "Aborting creation of Waterproof editor. Encountered a file with extension different from .mv, .v, or .lean!",
      );
      return;
    }
    this._format = format;
    this.initWebview(extensionUri);
  }

  private handleFileNameSaveAs(value: typeof SAVE_AS | undefined) {
    if (value === SAVE_AS)
      commands.executeCommand("workbench.action.files.saveAs");
  }

  /**
   * Create a ProseMirror webview.
   *
   * @param webviewPanel - VScode panel in which ProseMirror webview is displayed.
   * @param extensionUri - Uri of the directory containing Waterproof extension.
   * @param doc - Rocq of lean text document for which webview is created.
   * @param provider - Waterproof text editor provider.
   */
  public static async createWaterproofView(
    webviewPanel: WebviewPanel,
    extensionUri: Uri,
    doc: TextDocument,
    provider: WaterproofEditorProvider,
  ) {
    // Check if the line endings of file are windows
    if (doc.eol == EndOfLine.CRLF) {
      window.showErrorMessage(
        " Reopen the document!!! The document, you opened uses windows line endings (CRLF) and the editor does not support this! " +
          "We will convert the document to use unix line endings (LF).",
      );
      const editor = await window.showTextDocument(doc);
      if (editor !== null) {
        await editor.edit((builder) => {
          builder.setEndOfLine(EndOfLine.LF);
        });
        await commands.executeCommand("workbench.action.files.save");
        await commands.executeCommand("workbench.action.closeActiveEditor");
      } else {
        window.showErrorMessage("Failed to open document for conversion");
      }
    }
    return new WaterproofWebview(webviewPanel, extensionUri, doc, provider);
  }

  /**
   * Posts a message to the webview.
   * @param cache whether to store `message` and resend it after the editor reinitializes (default: `false`)
   */
  public postMessage(message: Message, cache: boolean = false) {
    this._panel.webview.postMessage(message);
    if (cache) {
      this._cachedMessages.set(message.type, message);
    }
  }

  /**
   * Get the document associated with the ProseMirror instance
   */
  public get document() {
    return this._document;
  }

  /**
   * Initialize the Waterproof webview
   *
   * @param extensionUri
   */
  private initWebview(extensionUri: Uri) {
    this._panel.webview.options = { enableScripts: true };

    // Convert path of `index.js` from local file uri to webview relative path.
    const scriptUri = this._panel.webview.asWebviewUri(
      Uri.joinPath(extensionUri, "editor_output", "index.js"),
    );

    // Convert path of `main.css` from local file uri to webview relative path.
    const styleUri = this._panel.webview.asWebviewUri(
      Uri.joinPath(extensionUri, "editor_output", "index.css"),
    );

    // Bring the editor up to date with changes made to the document outside of it: in a text
    // editor, by undo/redo there, by save actions such as trimming whitespace or formatting, or by
    // other extensions. Changes coming from the editor itself leave the two in sync.
    this._disposables.push(
      workspace.onDidChangeTextDocument((e) => {
        if (e.document.uri.toString() === this._document.uri.toString()) {
          this.refreshIfOutOfSync();
        }
      }),
    );

    this._disposables.push(
      workspace.onDidChangeConfiguration((e) => {
        if (e.affectsConfiguration("files", this._document)) {
          checkTextChangingSaveSettings(this._document);
        }

        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.TeacherMode),
          )
        ) {
          this.updateTeacherMode();
        }

        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.EnforceCorrectNonInputArea),
          )
        ) {
          this._enforceCorrectNonInputArea = WaterproofConfigHelper.get(
            WaterproofSetting.EnforceCorrectNonInputArea,
          );
        }

        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.ShowLineNumbersInEditor),
          )
        ) {
          this._showLineNrsInEditor = WaterproofConfigHelper.get(
            WaterproofSetting.ShowLineNumbersInEditor,
          );
          this.updateLineNumberStatusInEditor();
        }

        if (
          e.affectsConfiguration(
            qualifiedSettingName(WaterproofSetting.ShowMenuItemsInEditor),
          )
        ) {
          this._showMenuItemsInEditor = WaterproofConfigHelper.get(
            WaterproofSetting.ShowMenuItemsInEditor,
          );
          WaterproofLogger.log(
            `Menu items will now be ${this._showMenuItemsInEditor ? "shown" : "hidden"} in student mode`,
          );
          this.updateMenuItemsInEditor();
        }
      }),
    );

    this._disposables.push(
      this._panel.webview.onDidReceiveMessage((msg) => {
        this.handleMessage(msg);
      }),
    );

    this._disposables.push(
      window.onDidChangeActiveColorTheme(() => {
        // When the color theme changes we need to update the colors used for syntax highlighting
        this.themeUpdate();
      }),
    );

    this._disposables.push(
      this._panel.onDidDispose(() => {
        clearTimeout(this._readyTimeout);
        this._panel.dispose();
        for (const d of this._disposables) {
          d.dispose();
        }
        this.emit(WebviewEvents.dispose);
      }),
    );

    this._disposables.push(
      this._panel.onDidChangeViewState((e) => {
        if (e.webviewPanel.active) {
          // The editor is kept in sync with the document already, so it only needs to be
          // refreshed if that is still pending; re-initializing it would lose its position.
          this.refreshIfOutOfSync();
          this.sendEditorState();
          this.emit(WebviewEvents.change, WebviewState.focus);

          // Overwrite the undo and redo commands
          this._provider.registerHistoryCommandListeners(
            this,
            this.undoHandler.bind(this),
            this.redoHandler.bind(this),
          );
          // TODO: Handle this properly
          this.themeUpdate();
        } else {
          // Dispose of the overwritten undo and redo commands when the editor is not active.
          this._provider.disposeHistoryCommandListeners(this);
        }
      }),
    );

    // Get the nonce.
    const nonce = getNonce();

    const themeKind: "dark" | "light" = (() => {
      switch (window.activeColorTheme.kind) {
        case ColorThemeKind.HighContrast:
        case ColorThemeKind.Dark:
          return "dark";
        case ColorThemeKind.HighContrastLight:
        case ColorThemeKind.Light:
          return "light";
      }
    })();

    // Fill the webview panel with initial HTML of our ProseMirror based editor.
    this._panel.webview.html = `
        <!doctype html>
        <html>
        <head>
            <title>ProseMirror Math</title>
            <meta charset="utf-8">
            <script defer src="${scriptUri}" nonce="${nonce}"></script><link href="${styleUri}" rel="stylesheet">
        </head>
        <body format="${this._format}">
            <article>
                <!-- The div underneath stores the editor -->
                <div id="editor" spellcheck="false" data-theme-kind="${themeKind}">
                </div>
            </article>
            <div style="height: 50vh"></div>
            <!-- This div stores the editor content (not displayed) -->
            <div id="editor-content" style="display:none"></div>
        </body>
        </html>
        `;
    WaterproofLogger.debug(
      `[editor] webview html set for ${WaterproofFileUtil.getBasename(this._document.uri)}, script=${scriptUri}`,
    );
    this._readyTimeout = setTimeout(() => {
      this._readyTimeout = undefined;
      WaterproofLogger.log(
        `[editor] No 'ready' message from the editor webview after ${READY_TIMEOUT_MS}ms. ` +
          `The editor will stay blank. This usually means the bundle at ${scriptUri} ` +
          `failed to load or threw while evaluating; check the webview devtools ` +
          `(Developer: Open Webview Developer Tools).`,
      );
    }, READY_TIMEOUT_MS);

    // TODO: find a proper way to do this
    this.themeUpdate();
  }

  private themeUpdate() {
    // Get kind of active ColorTheme (dark or light)
    const themeType: ThemeStyle = (() => {
      switch (window.activeColorTheme.kind) {
        // TODO: For now HighContrast Light and Dark are
        // considered "normal" Light and Dark respectively.
        case ColorThemeKind.Dark:
        case ColorThemeKind.HighContrast:
          return ThemeStyle.Dark;
        case ColorThemeKind.Light:
        case ColorThemeKind.HighContrastLight:
          return ThemeStyle.Light;
      }
    })();
    this.postMessage(
      {
        type: MessageType.themeUpdate,
        body: {
          theme: themeType,
          lang: this.document.languageId,
        },
      },
      true,
    );
  }

  /**
   * Initializes a newly loaded editor with the document content. Only used when the webview
   * (re)loads, since it then has no content and has not sent any changes yet.
   */
  private syncWebview() {
    const text = this._document.getText();
    this._editorText = text;
    this._receivedChanges = 0;
    this._pendingRefresh = undefined;
    this.postMessage({
      type: MessageType.init,
      body: { value: text, version: this._document.version },
    });
    this.sendEditorState();
    // Edits from a previous instance of the editor may still be queued.
    this.refreshIfOutOfSync();
  }

  /** Sends the line number setting and the cached messages, which a (re)built editor needs. */
  private sendEditorState() {
    this.updateLineNumberStatusInEditor();
    for (const m of this._cachedMessages.values()) this.postMessage(m);
  }

  /**
   * Sends the document text to the editor if it differs from what the editor shows.
   *
   * This waits until the edits from the editor have been applied, since until then the document
   * is behind the editor, and until the editor has answered the previous refresh. The editor
   * rejects the refresh if it has sent changes that the extension had not received yet; the
   * extension then applies those and tries again.
   */
  private refreshIfOutOfSync() {
    if (
      this._workspaceEditor.isInProgress ||
      this._pendingRefresh !== undefined
    )
      return;
    const text = this._document.getText();
    if (text === this._editorText) return;

    this._pendingRefresh = text;
    this.postMessage({
      type: MessageType.refreshDocument,
      body: {
        value: text,
        version: this._document.version,
        receivedChanges: this._receivedChanges,
      },
    });
    // Refreshing replaces the editor state, which drops decorations such as diagnostics.
    this.sendEditorState();
  }

  /** Handles the editor's answer to a refresh. */
  private handleRefreshResult(accepted: boolean) {
    if (accepted && this._pendingRefresh !== undefined) {
      this._editorText = this._pendingRefresh;
    }
    this._pendingRefresh = undefined;
    this.refreshIfOutOfSync();
  }

  private updateLineNumberStatusInEditor() {
    this.postMessage(
      {
        type: MessageType.setShowLineNumbers,
        body: this._showLineNrsInEditor,
      },
      true,
    );
  }

  private updateMenuItemsInEditor() {
    this.postMessage(
      {
        type: MessageType.setShowMenuItems,
        body: this._showMenuItemsInEditor,
      },
      true,
    );
  }

  /** Toggle the teacher mode */
  private updateTeacherMode() {
    const mode = WaterproofConfigHelper.get(WaterproofSetting.TeacherMode);
    this._teacherMode = mode;
    this.postMessage(
      {
        type: MessageType.teacher,
        body: mode,
      },
      true,
    );
  }

  /** Apply new doc changes to the underlying file */
  private applyChangeToWorkspace(change: DocChange, edit: WorkspaceEdit) {
    if (change.startInFile === change.endInFile) {
      edit.insert(
        this.document.uri,
        this.document.positionAt(change.startInFile),
        change.finalText,
      );
    } else if (change.finalText.length === 0) {
      edit.delete(
        this.document.uri,
        new Range(
          this._document.positionAt(change.startInFile),
          this.document.positionAt(change.endInFile),
        ),
      );
    } else {
      edit.replace(
        this.document.uri,
        new Range(
          this._document.positionAt(change.startInFile),
          this.document.positionAt(change.endInFile),
        ),
        change.finalText,
      );
    }
  }

  // Restore the document to the last correct state, that is, a state for which the content
  //  outside of the <input-area> tags is correct.
  private restore() {
    this._workspaceEditor.edit((edit) => {
      edit.replace(
        this.document.uri,
        new Range(
          this._document.positionAt(0),
          this.document.positionAt(this.document.getText().length),
        ),
        this._lastCorrectDocString,
      );
    });
    // The editor is refreshed once the edit has been applied, since the document then differs
    // from the editor.
    this.document.save();
  }

  /** Handle a doc change sent from prosemirror */
  private handleChangeFromEditor(change: DocChange | WrappingDocChange) {
    // The change is expressed in offsets into the text the editor shows.
    const base = this._editorText;
    this._editorText = applyDocChange(base, change);
    this._receivedChanges++;

    this._workspaceEditor.edit((e) => {
      // By the time the edit is applied, the document may have been changed outside the editor
      // as well; move the change along with those changes.
      const mapped = mapDocChange(change, base, this._document.getText());
      if (mapped === undefined) {
        // Both changed the same text; the document wins, and the editor is refreshed after
        // the queue is drained.
        WaterproofLogger.log(
          "Dropped a change from the editor that conflicts with a change to the document",
        );
        return;
      }
      if ("firstEdit" in mapped) {
        this.applyChangeToWorkspace(mapped.firstEdit, e);
        this.applyChangeToWorkspace(mapped.secondEdit, e);
      } else {
        this.applyChangeToWorkspace(mapped, e);
      }
    });

    // If we are in teacher mode or we don't want to check for non input region correctness we skip it.
    if (!this._teacherMode && this._enforceCorrectNonInputArea) {
      let foundDefect = false;
      // Check the text as the editor shows it, since the edit may not have been applied yet.
      const nonInputRegions = getNonInputRegions(this._editorText);
      if (nonInputRegions.length !== this._nonInputRegions.length) {
        foundDefect = true;
      } else {
        for (let i = 0; i < this._nonInputRegions.length; i++) {
          if (this._nonInputRegions[i].content !== nonInputRegions[i].content) {
            foundDefect = true;
            break;
          }
        }
      }

      if (foundDefect) {
        showRestoreMessage(this.restore.bind(this));
      } else {
        this._lastCorrectDocString = this._editorText;
      }
    }
  }

  private sendHistoryChangeToEditor(type: HistoryChange) {
    this.postMessage({
      type: MessageType.editorHistoryChange,
      body: type,
    });
  }

  /** Handle the messages received from prosemirror */
  private handleMessage(msg: Message) {
    switch (msg.type) {
      case MessageType.docChange:
        this.handleChangeFromEditor(msg.body);
        break;
      case MessageType.refreshResult:
        this.handleRefreshResult(msg.body.accepted);
        break;
      case MessageType.ready:
        if (this._readyTimeout !== undefined) {
          clearTimeout(this._readyTimeout);
          this._readyTimeout = undefined;
        }
        WaterproofLogger.debug("[editor] webview reported ready, syncing");
        this.syncWebview();
        // When ready send the state of the teacher mode and show menu items settings to editor
        this.updateTeacherMode();
        this.updateMenuItemsInEditor();
        break;
      default:
        this.emit(WebviewEvents.message, msg);
        break;
    }
  }
}
