// Relevant imports
import { TextDocument } from "vscode";
import { FileFormat } from "../../shared";


/** Gets the file format from the text doc uri */
export function getFormatFromExtension(doc: TextDocument): FileFormat {
    // Get the parts from uri
    const uriParts = doc.uri.fsPath.split(".");
    // Get the extension
    console.log(uriParts)
    const extension = uriParts[uriParts.length - 1];
    for (let i = 0; i < uriParts.length-1; i++) {
        let substrings = [" ","-","(",")"]
        if (substrings.some(v => uriParts[i].includes(v))) {
            throw new Error("Filename can not include any of the following characters: \[space\],\-,\(,\)")
        }
    }
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