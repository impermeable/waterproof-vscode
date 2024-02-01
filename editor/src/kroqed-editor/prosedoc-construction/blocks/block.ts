import { Node as ProseNode } from "prosemirror-model";

// The different types of blocks that can be constructed.
export enum BLOCK_NAME {
    coq = "coq",
    math_display = "math_display", 
    input_area = "input_area",
    hint = "hint", 
    markdown = "markdown",
    coqdown = "coqdown"
}

export interface BlockRange {
    from: number;
    to: number;
}

export interface Block {
    type: string;
    stringContent: string;
    range: BlockRange;

    toProseMirror(): ProseNode | null;
}