import { Node as ProseNode } from "prosemirror-model";

// The different types of blocks that can be constructed.
export enum BLOCK_NAME {
    COQ = "coq",
    MATH_DISPLAY = "math_display", 
    INPUT_AREA = "input_area",
    HINT = "hint", 
    MARKDOWN = "markdown",
    COQ_MARKDOWN = "coqdown",
    COQ_CODE = "coq_code", 
    COQ_DOC = "coq_doc"
}

export interface BlockRange {
    from: number;
    to: number;
}

export interface Block {
    type: string;
    stringContent: string;
    range: BlockRange;

    innerBlocks?: Block[];

    toProseMirror(): ProseNode | null;
    debugPrint(level: number): void;
}