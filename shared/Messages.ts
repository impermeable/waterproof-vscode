import { DiagnosticSeverity } from "vscode";
import { FileFormat } from "./FileFormat";
import { LineNumber } from "./LineNumber";
import { DocChange, WrappingDocChange } from "./DocChange";
import { QedStatus } from "./QedStatus";
import { Completion } from "@codemirror/autocomplete";
import { GoalAnswer, PpString } from "../lib/types";

/** Type former for the `Message` type. A message has an optional body B, but must include a type T (from MessageType)
 *
 * Notes on the type former:
 * - T extends MessageType makes sure T is a member of the MessageType enum.
 * - B = undefined, defaults B to undefined (so we don't have to provide for messages that don't include a body)
 * - B extends undefined ? A : B, is the usual ternary operator `if`. When `B extends undefined` (B = undefined)
 *   then we choose A, otherwise (B is an object) we choose B.
 *
 * Ex: MessageBase<MessageType.ready> does not contain a body and expands to { type : MessageType.ready }
 *     MessageBase<MessageType.update, { value: string, version: number }> does contain a body and expands to
 *     {
 *          type: MessageType.update,
 *          body: { value: string, version: number }
 *     }
*/
type MessageBase<T extends MessageType, B = undefined> =
    B extends undefined ? { type: T, requestId?: number } : { type: T, body: B, requestId?: number };

export type Message =
    | MessageBase<MessageType.applyStepError, string>
    | MessageBase<MessageType.command, { command: string, time?: number}>
    | MessageBase<MessageType.cursorChange, number>
    | MessageBase<MessageType.diagnostics, DiagnosticMessage>
    | MessageBase<MessageType.docChange, DocChange | WrappingDocChange>
    | MessageBase<MessageType.editorHistoryChange, HistoryChangeType>
    | MessageBase<MessageType.editorReady>
    | MessageBase<MessageType.errorGoals, unknown>
    | MessageBase<MessageType.fatalError, { error: string }>
    | MessageBase<MessageType.init, { value: string, format: FileFormat, version: number }>
    | MessageBase<MessageType.insert, { symbolUnicode: string, symbolLatex: string, type: string, time: number }>
    | MessageBase<MessageType.lineNumbers, LineNumber>
    | MessageBase<MessageType.progress, SimpleProgressParams>
    | MessageBase<MessageType.qedStatus, QedStatus[]>
    | MessageBase<MessageType.ready>
    | MessageBase<MessageType.renderGoals, unknown>
    | MessageBase<MessageType.requestGoals, unknown>
    | MessageBase<MessageType.response, { data: unknown, requestId: number }>
    | MessageBase<MessageType.setAutocomplete, Completion[]>
    | MessageBase<MessageType.setData, string[] | GoalAnswer<PpString> >
    | MessageBase<MessageType.setShowLineNumbers, boolean>
    | MessageBase<MessageType.syntax, boolean>
    | MessageBase<MessageType.teacher, boolean>
    | MessageBase<MessageType.update, { value: string, version: number }>
    | MessageBase<MessageType.updateVersion, { version: number }>;

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
