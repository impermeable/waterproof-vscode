export type DocChange = NormalDocChange | WrappingDocChange;

export function isWrappingDocChange(change: DocChange): change is WrappingDocChange {
    return "firstEdit" in change;
}

/**
 * This object specifies a TextDocument change. As in prosemirror:
 * startInFile == endInFile: insert operation
 * else: replace or deletion with finalText
 */
export type NormalDocChange = {
    startInFile: number, // offset in TextDocument model
    endInFile: number,
    finalText: string, // new text in those positions of TextDocument model
}

export function isInsertDocChange(change: NormalDocChange): boolean {
    return change.startInFile === change.endInFile;
}

export function isDeleteDocChange(change: NormalDocChange): boolean {
    return change.finalText.length === 0
}

/**
 * This object specifies a wrapping TextDocument change. This happens when nodes
 * are wrapped with input or hint
 */
export type WrappingDocChange = {
    firstEdit: NormalDocChange,
    secondEdit: NormalDocChange,
}