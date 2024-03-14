import { EventEmitter } from "stream";
import { Disposable, EndOfLine, Position, Range, TextDocument, Uri, WebviewPanel, WorkspaceEdit, commands, window, workspace } from "vscode";

import { DocChange, FileFormat, Message, MessageType, WrappingDocChange, LineNumber } from "../../shared";
import { getNonce } from "../util";
import { WebviewEvents, WebviewState } from "../webviews/coqWebview";
import { SequentialEditor } from "./edit";
import {getFormatFromExtension, isIllegalFileName } from "./fileUtils";

const SAVE_AS = "Save As";
import { WaterproofConfigHelper, WaterproofLogger } from "../helpers";
import { getNonInputRegions, showRestoreMessage } from "./file-utils";

export class ProseMirrorWebview extends EventEmitter {
    /** The webview panel of this ProseMirror instance */
    private _panel: WebviewPanel;

    /** The document associated with this ProseMirror instance */
    private readonly _document: TextDocument;

    /** The file format of the doc associated with this ProseMirror instance */
    private readonly _format: FileFormat;

    /** The editor that appends changes to the document associated with this panel */
    private readonly _workspaceEditor = new SequentialEditor();

    /** Disposables */
    private readonly _disposables: Disposable[] = [];

    /** The latest linenumbers message */
    private _linenumber: LineNumber | undefined = undefined;

    private _teacherMode: boolean;
    private _enforceCorrectNonInputArea: boolean;
    private _lastCorrectDocString: string;

    /** These regions contain the strings that are outside of the <input-area> tags, but including the tags themselves */
    private _nonInputRegions: {
        to: number, 
        from: number, 
        content: string
     }[];

    /**
     * Collection of messages that were sent before, and should be resent if the editor
     * reinitializes (because the LSP server does not re-emit them if the document did not change).
     * Whether a message should be cached is specified in the `postMessage` method. Only one message
     * per type is cached.
     */
    private _cachedMessages: Map<MessageType, Message>;

    /** Checks whether the document is currently being changed */
    get documentIsUpToDate() {
        return !this._workspaceEditor.isInProgress;
    }

    private constructor(webview: WebviewPanel, extensionUri: Uri, doc: TextDocument) {
        super();

        var path = require('path')

        const fileName = path.basename(doc.uri.fsPath)
        
        if (isIllegalFileName(fileName)) {
            const error = `The file "${fileName}" cannot be opened, most likely because it either contains a space " ", or one of the characters: "\-", "\(", "\)". Please rename the file.`
            window.showErrorMessage(error, { modal: true }, SAVE_AS).then(this.handleFileNameSaveAs);
            WaterproofLogger.log("Error: Illegal file name encountered.");
        }

        this._format = getFormatFromExtension(doc);

        this._panel = webview;
        this._workspaceEditor.onFinish(() => {
            this.updateLineNumbers();
            this.emit(WebviewEvents.finishUpdate);
        });
        this._cachedMessages = new Map();
        this.initWebview(extensionUri);
        this._document = doc;

        this._nonInputRegions = getNonInputRegions(doc.getText());

        this._teacherMode = WaterproofConfigHelper.teacherMode;
        this._enforceCorrectNonInputArea = WaterproofConfigHelper.enforceCorrectNonInputArea;
        this._lastCorrectDocString = doc.getText();
    }

    private handleFileNameSaveAs(value: typeof SAVE_AS | undefined) {
        if (value === SAVE_AS) commands.executeCommand("workbench.action.files.saveAs");
    }

    /** Create a prosemirror webview */
    public static async createProseMirrorView(webview: WebviewPanel, extensionUri: Uri, doc: TextDocument) {
        // Check if the line endings of file are windows
        if (doc.eol == EndOfLine.CRLF) {
            window.showErrorMessage(" Reopen the document!!! The document, you opened uses windows line endings (CRLF) and the editor does not support this! " +
                "We will convert the document to use unix line endings (LF).");
            let editor = await window.showTextDocument(doc);
            if (editor !== null) {
                await editor.edit(builder => {
                    builder.setEndOfLine(EndOfLine.LF);
                });
                await commands.executeCommand('workbench.action.files.save');
                await commands.executeCommand('workbench.action.closeActiveEditor');
            } else {
                window.showErrorMessage("Failed to open document for conversion");
            }
        }
        return new ProseMirrorWebview(webview, extensionUri, doc);
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
     * Initialize the ProseMirror webview
     *
     * @param extensionUri
     */
    private initWebview(extensionUri: Uri) {
        this._panel.webview.options = { enableScripts: true };

        // Convert path of `index.js` from local file uri to webview relative path.
        const scriptUri = this._panel.webview.asWebviewUri(Uri.joinPath(
            extensionUri, 'editor_output', 'index.js'));

        // Convert path of `main.css` from local file uri to webview relative path.
        const styleUri = this._panel.webview.asWebviewUri(Uri.joinPath(
            extensionUri, 'editor_output', 'index.css'));

        // Register various listeners
        this._disposables.push(workspace.onDidChangeTextDocument(e => {
            if (!e.reason) return;
            if (e.document.uri.toString() === this._document.uri.toString()) {
                this.syncWebview();
            }
        }));

        this._disposables.push(workspace.onDidChangeConfiguration(e => {
            if (e.affectsConfiguration("waterproof.teacherMode")) {
                this.updateTeacherMode();
            }

            if (e.affectsConfiguration("waterproof.standardCoqSyntax")) {
                this.updateSyntaxMode();
            }

            if (e.affectsConfiguration("waterproof.enforceCorrectNonInputArea")) {
                this._enforceCorrectNonInputArea = WaterproofConfigHelper.enforceCorrectNonInputArea;
            }
        }));

        this._disposables.push(this._panel.webview.onDidReceiveMessage((msg) => {
            this.handleMessage(msg);
        }));

        this._disposables.push(this._panel.onDidDispose(() => {
            this._panel.dispose();
            for (let d of this._disposables) {
                d.dispose();
            }
            this.emit(WebviewEvents.dispose);
        }));

        this._disposables.push(this._panel.onDidChangeViewState((e) => {
            if (e.webviewPanel.active) {
                this.syncWebview();
                this.emit(WebviewEvents.change, WebviewState.focus);
            }
        }));

        // Get the nonce.
        const nonce = getNonce();

        this._panel.webview.html = `
        <!doctype html>
        <html>
        <head>
            <title>ProseMirror Math</title>
            <meta charset="utf-8">
            <script defer src="${scriptUri}" nonce="${nonce}"></script><link href="${styleUri}" rel="stylesheet">
        </head>
        <body>
            <article>
                <!-- The div underneath stores the editor -->
                <div id="editor" spellcheck="false">
                </div>
            </article>
            <div style="height: 50vh"></div>
            <!-- This div stores the editor content (not displayed) -->
            <div id="editor-content" style="display:none"></div>
        </body>
        </html>
        `;
    }

    private syncWebview() {
        // send document content
        this.postMessage({
            type: MessageType.init,
            body: {
                value: this._document.getText(),
                format: this._format,
                version: this._document.version,
            }
        });

        // send any cached messages
        for (const m of this._cachedMessages.values()) this.postMessage(m);
    }

    /** Convert line number offsets to line indices and send message to prose webview */
    private updateLineNumbers() {
        if (!this._linenumber || this._linenumber.version > this._document.version) return;
        this.postMessage({
            type: MessageType.lineNumbers,
            body: {
                linenumbers: this._linenumber.linenumbers.map(n => this._document.positionAt(n).line),
                version: this._document.version,
            }
        }, true);
    }

    /** Toggle the teacher mode */
    private updateTeacherMode() {
        const mode = WaterproofConfigHelper.teacherMode;
        this._teacherMode = mode;
        this.postMessage({
            type: MessageType.teacher,
            body: mode
        }, true);
    }

    /** Toggle the syntax mode*/
    private updateSyntaxMode() {
        this.postMessage({
            type: MessageType.syntax,
            body: WaterproofConfigHelper.standardCoqSyntax
        }, true);
    }

    /** Apply new doc changes to the underlying file */
    private applyChangeToWorkspace(change: DocChange, edit: WorkspaceEdit) {
        if (change.startInFile === change.endInFile) {
            edit.insert(
                this.document.uri,
                this.document.positionAt(change.startInFile),
                change.finalText
            );
        } else if (change.finalText.length === 0) {
            edit.delete(
                this.document.uri,
                new Range(this._document.positionAt(change.startInFile), this.document.positionAt(change.endInFile))
            );
        } else {
            edit.replace(
                this.document.uri,
                new Range(this._document.positionAt(change.startInFile), this.document.positionAt(change.endInFile)),
                change.finalText
            );
        }
    }

    // Restore the document to the last correct state, that is, a state for which the content 
    //  outside of the <input-area> tags is correct.
    private restore() {
        this._workspaceEditor.edit(edit => {
            edit.replace(
                this.document.uri,
                new Range(this._document.positionAt(0), this.document.positionAt(this.document.getText().length)),
                this._lastCorrectDocString
            )
        });
        // We save the document and call sync webview to make sure that the editor is up to date
        this.document.save().then(() => {
            this.syncWebview();
        });
    }

    /** Handle a doc change sent from prosemirror */
    private handleChangeFromEditor(change: DocChange | WrappingDocChange) {
        this._workspaceEditor.edit(e => {
            if ("firstEdit" in change) {
                this.applyChangeToWorkspace(change.firstEdit, e);
                this.applyChangeToWorkspace(change.secondEdit, e);
            } else {
                this.applyChangeToWorkspace(change, e);
            }
        });

        // If we are in teacher mode or we don't want to check for non input region correctness we skip it.
        if (!this._teacherMode && this._enforceCorrectNonInputArea) {
            let foundDefect = false;
            const nonInputRegions = getNonInputRegions(this._document.getText());
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
                this._lastCorrectDocString = this._document.getText();
            }
        }
    }

    /** Handle the messages received from prosemirror */
    private handleMessage(msg: Message) {
        switch (msg.type) {
            case MessageType.docChange:
                this.handleChangeFromEditor(msg.body);
                break;
            case MessageType.ready:
                this.syncWebview();
                this.updateTeacherMode();
                break;
            case MessageType.lineNumbers:
                this._linenumber = msg.body;
                this.updateLineNumbers();
                break;
            default:
                this.emit(WebviewEvents.message, msg);
                break;
        }
    }
}
