import { DiagnosticSeverity } from "vscode";

/**
 * Interface for the message types. Every message needs to have a `type`.
 * `body` and `requestID` are optional.
 */
export type Message = {
    type: MessageType;
    body?: any;
    requestId?: number;
    time?: number,
}

/**
 * Message type enum. Every message that is send from the
 * extension host to the editor (and vice versa) needs to have a type.
 */
export enum MessageType {
    response = "response",
    update = "update",
    init = "init",
    ready = "ready",
    /**
     * A notification sent from the editor to the extension when the editor is (1) initialized, or
     * (2) synched (e.g., after an undo, redo, or refocus).
     */
    editorReady = "editorReady",
    docChange = "docChange",
    cursorChange = "cursorChange",
    lineNumbers = "lineNumbers",
    requestGoals = "waitingForInfo",
    renderGoals = "renderGoals",
    errorGoals = "infoError", // this should probably be changed to a generic error message
    insert = "insertSymbol",
    command = "command",
    teacher = "toggleTeacherMode",
    setAutocomplete = "autocomplete",
    qedStatus = "qed",
    progress = "progress",
    diagnostics = "diagnostics",
    applyStepError = "applyStepError",
    fatalError = "fatal",
    updateVersion = "updateTextDocVersion",
    syntax= "setSyntaxMode",
}

export enum CoqFileProgressKind {
    Processing = 1,
    FatalError = 2,
}

export interface SimpleProgressInfo {
    /** Range for which the processing info was reported. */
    range: {
        start: { line: number, character: number },
        end: { line: number, character: number },
    };
    /** Kind of progress that was reported. */
    kind?: CoqFileProgressKind;
}

export interface SimpleProgressParams {
    numberOfLines: number;
    progress: SimpleProgressInfo[];
}

export interface OffsetDiagnostic {
    message: string;
    severity: DiagnosticSeverity;
    startOffset: number;
    endOffset: number;
}

export type DiagnosticMessage = {
    positionedDiagnostics: OffsetDiagnostic[],
    version: number
}
