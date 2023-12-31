import { Range } from "vscode";
import { NotificationType, RequestType } from "vscode-languageclient";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";

import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { CoqFileProgressKind, SimpleProgressInfo } from "../../shared";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const goalRequestType = new RequestType<GoalRequest, GoalAnswer<PpString>, void>("proof/goals");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const fileProgressNotificationType = new NotificationType<CoqFileProgressParams>("$/coq/fileProgress");

export interface CoqFileProgressProcessingInfo {
    /** Range for which the processing info was reported. */
    range: Range;
    /** Kind of progress that was reported. */
    kind?: CoqFileProgressKind;
}

export interface CoqFileProgressParams {
    /** The text document to which this progress notification applies. */
    textDocument: VersionedTextDocumentIdentifier;

    /**
     * Array containing the parts of the file which are still being processed.
     * The array should be empty if and only if the server is finished processing.
     */
    processing: CoqFileProgressProcessingInfo[];
}

/**
 * Converts `CoqFileProgressProcessingInfo` into `SimpleProgressInfo`. This is necessary(?) because
 * `vscode.Range.start` (and `end`) is secretly a function, which isn't retained when sent as a
 * message.
 */
export function convertToSimple(info: CoqFileProgressProcessingInfo): SimpleProgressInfo {
    const r = info.range;
    return {
        range: {
            start: { line: r.start.line, character: r.start.character },
            end:   { line: r.end.line,   character: r.end.character   }
        },
        kind: info.kind
    }
}
