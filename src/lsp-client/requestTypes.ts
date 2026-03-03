import { Range } from "vscode";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";

import { CoqFileProgressKind, SimpleProgressInfo } from "../../shared";

export interface FileProgressProcessingInfo {
    /** Range for which the processing info was reported. */
    range: Range;
    /**
     * Kind of progress that was reported.
     * Typed as `number` because it is a raw LSP wire value shared between
     * the Rocq and Lean clients (both use Processing = 1, FatalError = 2).
     */
    kind?: number;
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
        kind: info.kind as CoqFileProgressKind | undefined
    }
}
