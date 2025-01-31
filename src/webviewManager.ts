import { EventEmitter } from "stream";
import { TextDocument, Uri, window } from "vscode";

import { Message, MessageType } from "../shared";
import { IExecutor, ILineNumberComponent } from "./components";
import { LineStatusBar } from "./components/lineNumber";
import { ProseMirrorWebview } from "./pm-editor/pmWebview";
import { CoqWebview, WebviewEvents, WebviewState } from "./webviews/coqWebview";
import { Goal, GoalAnswer, Hyp, Pp, PpString, convertToString } from "../lib/types";
import { Message as GoalMessage } from "../lib/types";
import { FormatPrettyPrint } from "../lib/format-pprint/js/main";
import { GoalsPanel } from "./webviews/goalviews/goalsPanel";

export enum WebviewManagerEvents {
    editorReady     = "ready",
    focus           = "focus",
    cursorChange    = "cursorChange",
    command         = "command",
    updateButton    = "updateButton"
}

/**
 * Utility data structure to store webviews and retrieve them based on time.
 */
class ActiveWebviews {
    /** Timestamp date object */
    private readonly _date;

    /** A store for the last active webviews */
    private readonly _web: Map<number,string>;

    /** A double ended queue to allow for efficient timestamp manipulations */
    private readonly _queue;

    constructor() {
        this._date = new Date();
        this._web = new Map<number, string>();
        this._queue = new Array<number>();
    }

    public insert(id: string) {
        // Maybe add error handling for id not existing
        var time: number = Date.now();
        this._web.set(time, id);
        this._queue.unshift(time);
        if (this._queue.length == 20) {
            // @ts-ignore
            this._web.delete(this._queue.pop());
        }
    }

    /**
     * Returns the ID of the chronologically first webview after `times`.
     */
    public find(time: number) {
        var i: number = 0;
        if (this._queue.length == 0) throw new Error("There are no active panels");
        // @ts-ignore
        while (this._queue[i] >= time) { // There may be an issue where a panel supports insert and can send insert messages
            i++;
            if (this._queue.length == i) throw new Error("There are no valid active panels");
        }
        // @ts-ignore
        return this._web.get(this._queue[i]);
    }
}


/**
 * The webview manager that manages communication between views
 */
export class WebviewManager extends EventEmitter {
    // Tool webviews (UI such as panels), stores the view based on name
    private readonly _toolWebviews: Map<string, CoqWebview> = new Map<string, CoqWebview>;

    // ProseMirror webviews, stores the view based on Doc uri
    private readonly _pmWebviews: Map<string, ProseMirrorWebview> = new Map<string, ProseMirrorWebview>;

    // RequestId of request response
    private _requestId: number;

    // Callbacks used by request, response pattern
    private readonly _callbacks: Map<number, (response: any) => void> = new Map<number, (response: any) => void>;

    // StatusBar item that indicates line number and column position
    private readonly _lineStatus: ILineNumberComponent;

    // Manage the currently active webviews
    private readonly _active: ActiveWebviews;

    // Add singleton design pattern?
    constructor() {
        super();
        this._requestId = 1;
        this._lineStatus = new LineStatusBar();
        this._active = new ActiveWebviews();
    }

    public has(obj: string | TextDocument) {
        return typeof obj === "object"
            ? this._pmWebviews.has(obj.uri.toString())
            : this._pmWebviews.has(obj) || this._toolWebviews.has(obj);
    }

    /**
     * Add a tool webview to manager
     * @param name of the webview
     * @param webview object associated with tool
     */
    public addToolWebview(name: string, webview: CoqWebview) {
        if (this.has(name)) {
            throw new Error(" Webview already registered!  THIS SHOULD NOT HAPPEN! ");
        }
        this._toolWebviews.set(name, webview);
        webview.on(WebviewEvents.message, (msg: Message) => {
            this.onToolsMessage(name, msg);
        });
        webview.on(WebviewEvents.change, (state) => {
            if (state == WebviewState.focus && webview.supportInsert) this._active.insert(name);
            this.emit(WebviewManagerEvents.updateButton, { name, open: webview.isOpened});
        });
    }

    /**
     * Add a ProseMirror webview to manager
     * @param webview object associated with document
     */
    public addProseMirrorWebview(webview: ProseMirrorWebview) {

        if (this.has(webview.document)) {
            throw new Error(" Webview already registered!  THIS SHOULD NOT HAPPEN! ");
        }
        this._pmWebviews.set(webview.document.uri.toString(), webview);

        webview.on(WebviewEvents.dispose, () => {
            this._pmWebviews.delete(webview.document.uri.toString());
        });
        webview.on(WebviewEvents.message, (msg) => {
            this.onProseMessage(webview.document, msg);
        });
        webview.on(WebviewEvents.change, (state) => {
            if (state == WebviewState.focus) {
                this._active.insert(webview.document.uri.toString());
                this.emit(WebviewManagerEvents.focus, webview.document);
            }
        });

        this._active.insert(webview.document.uri.toString());
        this.emit(WebviewManagerEvents.focus, webview.document);
    }

    /**
     * Opens a tool webview to the user
     * @param id the id of the tool webview
     */
    public open(id: string) {
        if (this._toolWebviews.has(id)) new Error("Tool webview does not have this panel: " + id);
        this._toolWebviews.get(id)?.readyPanel();
        this._toolWebviews.get(id)?.activatePanel();
    }

    /**
     * Reveals a panel to the user
     * @param id the id of the tool webview
     */
    public reveal(id: string) {
        if (this._toolWebviews.has(id)) new Error("Tool webview does not have this panel: " + id);
        console.log(this._toolWebviews)
        this._toolWebviews.get(id)?.revealPanel()
    }

    /**
     * Sends `message` to the specified panel.
     * @param panelName a URI to refer to a ProseMirror panel, or a name to refer to a tool panel
     */
    public postMessage(panelName: string, message: Message) {
        if (this._pmWebviews.has(panelName))
            this._pmWebviews.get(panelName)?.postMessage(message);
        else if (this._toolWebviews.has(panelName))
            this._toolWebviews.get(panelName)?.postMessage(message);
        else
            throw new Error(" No such webview available ");
    }

    /**
     * Sends `message` to the ProseMirror webview identified by `documentUri`. The webview caches
     * this message, which means it's sent again when the editor reinitializes.
     */
    public postAndCacheMessage(documentUri: string | Uri | TextDocument, message: Message) {
        if (typeof documentUri === "object") {
            if ("uri" in documentUri) documentUri = documentUri.uri;
            documentUri = documentUri.toString();
        }
        const webview = this._pmWebviews.get(documentUri);
        if (!webview) throw new Error("There is no ProseMirror webview with URI: " + documentUri);
        webview.postMessage(message, true);
    }

    /**
     * Post a message for which we expect a response.
     * @param panel The panel to send the message to.
     * @param type The type of the message.
     * @param body The body of the message.
     * @returns A promise that is fulfilled when the response is received.
     */
    public postMessageWithResponse<R = unknown>(panel: string, type: MessageType, body: any): Promise<R> {
        const requestId = this._requestId++;
        const p = new Promise<R>(resolve => this._callbacks.set(requestId, resolve));
        //@ts-ignore
        this.postMessage(panel, { type, requestId, body });
        return p;
    }

    /**
     * Called when a message from the webview panel is received.
     *
     * @param document The `coqEditorDocument` the message originated from.
     * @param message The message.
     */
    private onProseMessage(document: TextDocument, message: Message) {
        // TODO: For now console.log the document and the message.
        switch (message.type) {
            case MessageType.response:
                // Response type message, look to which promise this belongs.
                if (!message.body.requestId) {
                    console.error("Received response message without a requestId!\nThe message:", message);
                    return;
                }
                const callback = this._callbacks.get(message.body.requestId);  // TODO: remove callback?
                callback?.(message.body);
                break;
            case MessageType.editorReady:
                this.emit(WebviewManagerEvents.editorReady, document);
                break;
            case MessageType.cursorChange:
                var pos = document.positionAt(message.body);
                this._lineStatus.update(pos);
                // Update goals components
                const webview = this._pmWebviews.get(document.uri.toString());
                if (!webview) break;
                if (webview.documentIsUpToDate) {
                    this.emit(WebviewManagerEvents.cursorChange, document, pos);
                } else {
                    // Document is updating wait for completion
                    const callback = () => {
                        this.emit(WebviewManagerEvents.cursorChange, document, pos);
                    };
                    if(webview.listeners(WebviewEvents.finishUpdate).length == 0) webview.once(WebviewEvents.finishUpdate, callback);
                }
                break;
            case MessageType.applyStepError:
                let mes = "File frozen due to corruption. Re-open the file. Error: " + message.body;
                window.showErrorMessage(mes);
                break;
            case MessageType.command:
                // We intercept the `command` type message here, since it can be fired from within the editor (rmb -> Help)
                this.onToolsMessage("help", {type: MessageType.command, body: { command: "createHelp"}});
                setTimeout(() => this.onToolsMessage("help", {type: MessageType.command, body: { command: "Help."}}), 250);
                break;
            default:
                console.error(`Unrecognized message type ${message.type}, not handled by webview manager`);
                break;
        }
    }

    /**
     * Called when a message from the webview panel is received.
     *
     * @param id The id of the webview
     * @param message The message.
     */
    private onToolsMessage(id: string, msg: Message) {
        switch (msg.type) {
            case MessageType.insert:
                // @ts-ignore
                var id: string = this._active.find(msg.time);
                this.postMessage(id, { type: MessageType.insert, body: msg.body });
                break;
            case MessageType.command:
                this.emit(WebviewManagerEvents.command, this._toolWebviews.get(id), msg.body);
                break;
            default:
                console.error("The message type " + msg.type + " is not currently supported by webview manager");
                break;
        }
    }

}


