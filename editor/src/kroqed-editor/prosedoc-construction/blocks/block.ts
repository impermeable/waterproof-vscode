import { Node as ProseNode } from "prosemirror-model";

// The different types of blocks that can be constructed.
export enum BLOCK_NAME {
    MATH_DISPLAY = "math_display", 
    INPUT_AREA = "input_area",
    HINT = "hint", 
    MARKDOWN = "markdown",
    CODE = "code", 
}

export interface BlockRange {
    from: number;
    to: number;
}

export interface Block {
    type: string;
    stringContent: string;
    /** Range in the original document, including possible tags (like <input-area>) */
    range: BlockRange;
    /** Range in the original document, but only the content within possible tags */
    innerRange: BlockRange;

    /** Blocks that are children of this block, only valid for InputArea and Hint Blocks. */
    innerBlocks?: Block[];

    /** Convert this block to the corresponding ProseMirror node. */
    toProseMirror(): ProseNode;
    debugPrint(level: number): void;
}