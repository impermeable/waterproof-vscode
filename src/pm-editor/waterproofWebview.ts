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

import { getNonce } from "../util";
import { WebviewEvents, WebviewState } from "../webviews/waterproofPanel";
import { DocumentSync, EditorChange, TextEdit } from "./documentSync";
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
import { HistoryChange, ThemeStyle } from "@impermeable/waterproof-editor";

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

  /** Keeps the editor and the document in sync. */
  private readonly _sync: DocumentSync;

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
   * Watchdog for the editor bundle: the webview only renders once it has sent
   * `MessageType.ready`, at which point we answer with the document contents. If
   * `editor_output/index.js` fails to load or throws while evaluating, that
   * message never arrives and the editor stays blank with no error on the
   * extension side, so time it out and say so.
   */
  private _readyTimeout?: ReturnType<typeof setTimeout>;

  /** Checks whether the document is currently being changed */
  get documentIsUpToDate() {
    return !this._sync.editsInProgress;
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
    this._cachedMessages = new Map();
    this._document = doc;

    this._sync = new DocumentSync({
      documentText: () => this._document.getText(),
      documentVersion: () => this._document.version,
      applyEdits: (edits) => workspace.applyEdit(this.workspaceEdit(edits)),
      sendInit: (text, version, generation, webview) =>
        this.sendInit(text, version, generation, webview),
      reportDiscardedChanges: (count) => {
        window.showWarningMessage(
          `${count} change(s) made in the Waterproof editor were discarded, because the ` +
            `file was changed elsewhere at the same time. The editor now shows the file.`,
        );
      },
      editsFinished: () => this.emit(WebviewEvents.finishUpdate),
      log: (message) => WaterproofLogger.log(message),
    });

    this._nonInputRegions = getNonInputRegions(doc.getText());

    this._teacherMode = WaterproofConfigHelper.get(
      WaterproofSetting.TeacherMode,
    );
    this._enforceCorrectNonInputArea = WaterproofConfigHelper.get(
      WaterproofSetting.EnforceCorrectNonInputArea,
    );
    this._lastCorrectDocString = doc.getText();

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

    // Changes made elsewhere (a text editor, undo there, save actions, other extensions) are
    // brought to the editor.
    this._disposables.push(
      workspace.onDidChangeTextDocument((e) => {
        if (e.document.uri.toString() === this._document.uri.toString()) {
          this._sync.documentChanged();
        }
      }),
    );

    this._disposables.push(
      workspace.onDidChangeConfiguration((e) => {
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
        this._sync.dispose();
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

  /** (Re)initializes the editor with `text`, and sends the state a new editor needs. */
  private sendInit(
    text: string,
    version: number,
    generation: number,
    webview: string,
  ) {
    this.postMessage({
      type: MessageType.init,
      body: { value: text, version, generation, webview },
    });

    this.updateLineNumberStatusInEditor();

    // send any cached messages
    for (const m of this._cachedMessages.values()) this.postMessage(m);
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

  /** A workspace edit with `edits`, expressed in offsets into the current document. */
  private workspaceEdit(edits: TextEdit[]): WorkspaceEdit {
    const edit = new WorkspaceEdit();
    for (const { start, end, text } of edits) {
      edit.replace(
        this._document.uri,
        new Range(
          this._document.positionAt(start),
          this._document.positionAt(end),
        ),
        text,
      );
    }
    return edit;
  }

  // Restore the document to the last correct state, that is, a state for which the content
  //  outside of the <input-area> tags is correct.
  private restore() {
    this._sync.replaceDocument(this._lastCorrectDocString);
  }

  /** Handle a doc change sent from prosemirror */
  private handleChangeFromEditor(change: EditorChange, generation: number) {
    const editorText = this._sync.changeFromEditor(change, generation);
    if (editorText === undefined) return;

    // If we are in teacher mode or we don't want to check for non input region correctness we skip it.
    if (!this._teacherMode && this._enforceCorrectNonInputArea) {
      let foundDefect = false;
      // Check the text as the editor shows it; the change may not have been applied yet.
      const nonInputRegions = getNonInputRegions(editorText);
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
        this._lastCorrectDocString = editorText;
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
        this.handleChangeFromEditor(msg.body.change, msg.body.generation);
        break;
      case MessageType.ready:
        if (this._readyTimeout !== undefined) {
          clearTimeout(this._readyTimeout);
          this._readyTimeout = undefined;
        }
        WaterproofLogger.debug("[editor] webview reported ready, syncing");
        // Send the state of the teacher mode and show menu items settings to editor. These are
        // cached, and so are sent again after the content.
        this.updateTeacherMode();
        this.updateMenuItemsInEditor();
        this._sync.editorReady(msg.body.webview);
        break;
      default:
        this.emit(WebviewEvents.message, msg);
        break;
    }
  }
}
