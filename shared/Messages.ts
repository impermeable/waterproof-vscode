import { DiagnosticSeverity } from "vscode";
import { FileFormat } from "./FileFormat";
import { LineNumber } from "./LineNumber";
import { DocChange, WrappingDocChange } from "./DocChange";
import { QedStatus } from "./QedStatus";
import { Completion } from "@codemirror/autocomplete";
import { GoalAnswer, PpString } from "../lib/types";

type MessageBase<T extends MessageType, B = undefined> =
    B extends undefined? { type: T, requestId?: number } : { type: T, body: B, requestId?: number };

export type Message =
    | MessageBase<MessageType.response, { data: any, requestId: number }>
    | MessageBase<MessageType.update, { value: string, version: number }>
    | MessageBase<MessageType.init, { value: string, format: FileFormat, version: number }>
    | MessageBase<MessageType.ready>
    | MessageBase<MessageType.editorReady>
    | MessageBase<MessageType.docChange, DocChange | WrappingDocChange>
    | MessageBase<MessageType.cursorChange, number>
    | MessageBase<MessageType.lineNumbers, LineNumber>
    | MessageBase<MessageType.requestGoals, any>
    | MessageBase<MessageType.renderGoals, any>
    | MessageBase<MessageType.errorGoals, { error: string }>
    | MessageBase<MessageType.insert, { symbolUnicode: string, symbolLatex: string, type: string }>
    | MessageBase<MessageType.command, { command: string, time?: number}>
    | MessageBase<MessageType.setData, string[] | GoalAnswer<PpString> >
    | MessageBase<MessageType.teacher, boolean>
    | MessageBase<MessageType.setAutocomplete, Completion[]>
    | MessageBase<MessageType.qedStatus, QedStatus[]>
    | MessageBase<MessageType.progress, SimpleProgressParams>
    | MessageBase<MessageType.diagnostics, DiagnosticMessage>
    | MessageBase<MessageType.applyStepError, string>
    | MessageBase<MessageType.fatalError, { error: string }>
    | MessageBase<MessageType.updateVersion, { version: number }>
    | MessageBase<MessageType.syntax, boolean>
    | MessageBase<MessageType.editorHistoryChange, HistoryChangeType>
    | MessageBase<MessageType.setShowLineNumbers, boolean>;

/**
 * Message type enum. Every message that is send from the
 * extension host to the editor (and vice versa) needs to have a type.
 */
export const enum MessageType {
    response,
    update,
    init,
    ready,
    editorReady,
    docChange,
    cursorChange,
    lineNumbers,
    requestGoals,
    renderGoals,
    errorGoals,
    insert,
    command,
    teacher,
    setAutocomplete,
    qedStatus,
    progress,
    diagnostics,
    applyStepError,
    fatalError,
    updateVersion,
    syntax,
    editorHistoryChange,
    setShowLineNumbers,
    setData,
}

export const enum HistoryChangeType {
    Undo,
    Redo
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
