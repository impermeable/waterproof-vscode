/**
 * This object specifies a TextDocument change. As in prosemirror:
 * startInFile == endInFile: insert operation
 * else: replace or deletion with finalText
 */
export type DocChange = {
    startInFile: number, // offset in TextDocument model
    endInFile: number,
    finalText: string, // new text in those positions of TextDocument model
}

/**
 * This object specifies a wrapping TextDocument change. This happens when nodes
 * are wrapped with input or hint
 */
export type WrappingDocChange = {
    firstEdit: DocChange,
    secondEdit: DocChange,
}