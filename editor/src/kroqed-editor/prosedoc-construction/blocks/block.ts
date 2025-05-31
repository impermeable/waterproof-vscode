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
    range: BlockRange;

    innerBlocks?: Block[];

    toProseMirror(): ProseNode;
    debugPrint(level: number): void;
}