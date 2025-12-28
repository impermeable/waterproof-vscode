import { Range, TextDocument } from "vscode";
import { NotificationType, RequestType } from "vscode-languageclient";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";

import { CoqServerStatus, GoalAnswer, GoalRequest, PpString } from "../../lib/types";
import { CoqFileProgressKind, SimpleProgressParams } from "@impermeable/waterproof-editor";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const goalRequestType = new RequestType<GoalRequest, GoalAnswer<PpString>, void>("proof/goals");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const fileProgressNotificationType = new NotificationType<CoqFileProgressParams>("$/coq/fileProgress");

/**
 * Notification type for the coq-lsp specific `serverStatus` notification. Returns a `CoqServerStatus` object that
 * can be either Busy or Idle.
 */
export const serverStatusNotificationType = new NotificationType<CoqServerStatus>("$/coq/serverStatus");

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

/** Converts a CoqFileProgressParams object that we received from rocq-lsp into a type that we can sent to waterproof-editor */
export function convertToSimple(document: TextDocument, info: CoqFileProgressParams): SimpleProgressParams {
    if (info.processing.length < 1) throw new Error("No processing info in CoqFileProgressParams object");
    const p = info.processing[0];
    const r = p.range;
    return {
        numberOfLines: document.lineCount,
        progress: {
            range: {
                start: { line: r.start.line, character: r.start.character },
                end:   { line: r.end.line,   character: r.end.character   }
            },
            offsetRange: {
                start: document.offsetAt(r.start),
                end: document.offsetAt(r.end)
            },
            kind: p.kind
        }
    }
}