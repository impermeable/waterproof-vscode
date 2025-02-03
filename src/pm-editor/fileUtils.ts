// Relevant imports
import { TextDocument } from "vscode";
import { FileFormat } from "../../shared";


/** Gets the file format from the text doc uri */
export function getFormatFromExtension(doc: TextDocument): FileFormat {
    // Get the parts from uri
    const uriParts = doc.uri.fsPath.split(".");
    // Get the extension
    const extension = uriParts[uriParts.length - 1];

    // Return the correct file format
    if (extension === "mv") {
        return FileFormat.MarkdownV;
    } else if (extension === "v") {
        return FileFormat.RegularV;
    } else {
        // Unknown filed type this should not happen
        return FileFormat.Unknown;
    }
}

export function isIllegalFileName(fileName: string): boolean {
    const substrings = [" ","-","(",")"]
    if (substrings.some(v => fileName.includes(v))) {
        return true;
    }
    // If we reach this return then that means we have not found any illegal characters in the file name.
    return false;
}