import { LineNumber, DocChange, WrappingDocChange, InputAreaStatus, HistoryChange, DiagnosticMessage, SimpleProgressParams, ServerStatus, ThemeStyle } from "@impermeable/waterproof-editor";
import { GoalAnswer, HypVisibility, PpString } from "../lib/types";
import { Completion } from "@impermeable/waterproof-editor";


/** Type former for the `Message` type. A message has an optional body B, but must include a type T (from MessageType)
 *
 * Notes on the type former:
 * - T extends MessageType makes sure T is a member of the MessageType enum.
 * - B = undefined, defaults B to undefined (so we don't have to provide for messages that don't include a body)
 * - B extends undefined ? A : B, is the usual ternary operator `if`. When `B extends undefined` (B = undefined)
 *   then we choose A, otherwise (B is an object) we choose B.
 *
 * Ex: MessageBase<MessageType.ready> does not contain a body and expands to { type : MessageType.ready }
 *     MessageBase<MessageType.command, { command: string, time?: number}> does contain a body and expands to
 *     {
 *         command: string,
 *         time?: number
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
    | MessageBase<MessageType.editorHistoryChange, HistoryChange>
    | MessageBase<MessageType.editorReady>
    | MessageBase<MessageType.errorGoals, unknown>
    | MessageBase<MessageType.init, { value: string, version: number }>
    | MessageBase<MessageType.insert, { symbolUnicode: string, type: "symbol" | "tactics", time: number }>
    | MessageBase<MessageType.lineNumbers, LineNumber>
    | MessageBase<MessageType.progress, SimpleProgressParams>
    | MessageBase<MessageType.qedStatus, InputAreaStatus[]>
    | MessageBase<MessageType.ready>
    | MessageBase<MessageType.renderGoals, { goals : GoalAnswer<PpString>, visibility?: HypVisibility }>
    | MessageBase<MessageType.renderGoalsList, { goalsList : GoalAnswer<PpString>[]}>
    | MessageBase<MessageType.response, { data: unknown, requestId: number }>
    | MessageBase<MessageType.serverStatus, ServerStatus>
    | MessageBase<MessageType.setAutocomplete, Completion[]>
    | MessageBase<MessageType.setData, string[] | GoalAnswer<PpString> >
    | MessageBase<MessageType.setShowLineNumbers, boolean>
    | MessageBase<MessageType.setShowMenuItems, boolean>
    | MessageBase<MessageType.teacher, boolean>
    | MessageBase<MessageType.themeUpdate, ThemeStyle>
    | MessageBase<MessageType.viewportHint, { start: number, end: number }>;

/**
 * Message type enum. Every message that is send from the
 * extension host to the editor (and vice versa) needs to have a type.
 */
export const enum MessageType {
    applyStepError,
    command,
    cursorChange,
    diagnostics,
    docChange,
    editorHistoryChange,
    editorReady,
    errorGoals,
    init,
    insert,
    lineNumbers,
    progress,
    qedStatus,
    ready,
    renderGoals,
    renderGoalsList,
    response,
    serverStatus,
    setAutocomplete,
    setData,
    setShowLineNumbers,
    setShowMenuItems,
    teacher,
    themeUpdate,
    flash,
    viewportHint,
}
