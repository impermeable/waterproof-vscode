
/**
 * This is the versioned linenumber message
 */
export type LineNumber = {
    /** The linenumbers */
    linenumbers: Array<number>, 
    /** Version of the document the linenumbers correspond to.. */
    version: number,
}