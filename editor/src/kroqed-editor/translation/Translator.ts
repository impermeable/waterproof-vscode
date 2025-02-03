import { translateMvToProsemirror } from "./toProsemirror";
import { FileFormat } from "../../../../shared"

/** Class that handles the translation from .mv | .v to prosemirror and vice versa. */
export class FileTranslator {
    private _filef: FileFormat;

    /**
     * Create a new file format translator. 
     * @param fileFormat The input file format to use. Can be either `FileFormat.MarkdownV` for .mv files or
     * `FileFormat.RegularV` for regular coq files.
     */
    constructor(fileFormat: FileFormat) {
        this._filef = fileFormat;
        switch (this._filef) {
            case FileFormat.Unknown: 
                throw new Error("Cannot initialize Translator for `unknown` file type.");
        }
    }
    
    /**
     * Get the file format this FileTranslator was configured for.
     */
    public get fileFormat() {
        return this._filef;
    }

    /**
     * Convert an input file to a prosemirror compatible HTML representation. 
     * Input format is set by `fileFormat` in the constructor.
     * @param inputDocument The input document read from disk. 
     * @returns A prosemirror compatible HTML document (as string).
     */
    public toProsemirror(inputDocument: string): string {
        switch (this._filef) {
            case FileFormat.MarkdownV:
                return translateMvToProsemirror(inputDocument); // 
            case FileFormat.RegularV:
                // TODO: Parser for regular .v
                return translateMvToProsemirror(inputDocument);
            case FileFormat.Unknown: 
                throw new Error("Cannot convert from unknown format");
        }
    }
}
