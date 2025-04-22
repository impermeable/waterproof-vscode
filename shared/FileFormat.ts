/**
 * The different supported input/output file types
 */
export enum FileFormat {
    /** Markdown enabled coq file (extension: `.mv`) */
    MarkdownV = "MarkdownV",
    /** Regular coq file, with the possibility for coqdoc comments (extension: `.v`) */
    RegularV = "RegularV"
}
