import { Node as PNode } from "prosemirror-model";
import { coq, coqDown, hint, inputArea, markdown, mathDisplay, text } from "./pm-node-constructors";

export enum BLOCK_NAME {
    coq = "coq",
    math_display = "math_display", 
    input_area = "input_area",
    hint = "hint", 
    markdown = "markdown",
    coqdown = "coqdown"
}

interface BlockRange {
    to: number,
    from: number
}

export interface Block {
    name: string;
    content: string;
    range: BlockRange;

    toProseMirror(): PNode;
}

export const isCoqBlock = (block: Block): block is CoqBlock => block.name === BLOCK_NAME.coq;

export class CoqBlock implements Block {
    public name = BLOCK_NAME.coq;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return coq(this.content);
    }
}

export const isMathDisplayBlock = (block: Block): block is MathDisplayBlock => block.name === BLOCK_NAME.math_display;

export class MathDisplayBlock implements Block {
    public name = BLOCK_NAME.math_display;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return mathDisplay(this.content);
    }
}

export const isInputAreaBlock = (block: Block): block is InputAreaBlock => block.name === BLOCK_NAME.input_area;

export class InputAreaBlock implements Block {
    public name = BLOCK_NAME.input_area;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return inputArea(this.content);
    }
}

export const isHintBlock = (block: Block): block is HintBlock => block.name === BLOCK_NAME.hint;

export class HintBlock implements Block {
    public name = BLOCK_NAME.hint;
    constructor( public content: string, public title: string, public range: BlockRange ) {};

    toProseMirror() {
        return hint(this.title, this.content);
    }
}

export const isMarkdownBlock = (block: Block): block is MarkdownBlock => block.name === BLOCK_NAME.markdown;

export class MarkdownBlock implements Block {
    public name = BLOCK_NAME.markdown;
    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return markdown(this.content);
    }
}

export const isCoqDownBlock = (block: Block): block is CoqdownBlock => block.name === BLOCK_NAME.coqdown;

export class CoqdownBlock implements Block {
    public name = BLOCK_NAME.coqdown;

    constructor( public content: string, public range: BlockRange ) {};

    toProseMirror() {
        return coqDown(this.content);
    }
}