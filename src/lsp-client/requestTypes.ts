import { Range } from "vscode";
import { NotificationType, RequestType } from "vscode-languageclient";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";

import { CoqServerStatus, CoqGoalAnswer, CoqGoalRequest, PpString, LeanGoalRequest, LeanGoalAnswer } from "../../lib/types";
import { FileProgressKind, SimpleProgressInfo } from "@impermeable/waterproof-editor";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const coqGoalRequestType = new RequestType<CoqGoalRequest, CoqGoalAnswer<PpString>, void>("proof/goals");
export const leanGoalRequestType = new RequestType<LeanGoalRequest, LeanGoalAnswer, void>("$/lean/plainGoal");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const coqFileProgressNotificationType = new NotificationType<FileProgressParams>("$/coq/fileProgress");
export const leanFileProgressNotificationType = new NotificationType<FileProgressParams>("$/lean/fileProgress");

/**
 * Notification type for the coq-lsp specific `serverStatus` notification. Returns a `CoqServerStatus` object that
 * can be either Busy or Idle.
 */
export const serverStatusNotificationType = new NotificationType<CoqServerStatus>("$/coq/serverStatus");

export interface FileProgressProcessingInfo {
    /** Range for which the processing info was reported. */
    range: Range;
    /** Kind of progress that was reported. */
    kind?: FileProgressKind;
}

export interface FileProgressParams {
    /** The text document to which this progress notification applies. */
    textDocument: VersionedTextDocumentIdentifier;

    /**
     * Array containing the parts of the file which are still being processed.
     * The array should be empty if and only if the server is finished processing.
     */
    processing: FileProgressProcessingInfo[];
}

/**
 * Converts `CoqFileProgressProcessingInfo` into `SimpleProgressInfo`. This is necessary(?) because
 * `vscode.Range.start` (and `end`) is secretly a function, which isn't retained when sent as a
 * message.
 */
export function convertToSimple(info: FileProgressProcessingInfo): SimpleProgressInfo {
    const r = info.range;
    return {
        range: {
            start: { line: r.start.line, character: r.start.character },
            end:   { line: r.end.line,   character: r.end.character   }
        },
        kind: info.kind
    }
}
