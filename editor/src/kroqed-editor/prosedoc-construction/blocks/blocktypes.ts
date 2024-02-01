import { BLOCK_NAME, Block, BlockRange } from "./block";

export class InputAreaBlock implements Block {
    public type = BLOCK_NAME.input_area;
    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        // TODO
        return null;
    }
}

export class HintBlock implements Block {
    public type = BLOCK_NAME.hint;

    // Note: Hint blocks have a title attribute.
    constructor( public stringContent: string, public title: string, public range: BlockRange ) {};

    toProseMirror() {
        // TODO
        return null;
    }
}

export class MathDisplayBlock implements Block {
    public type = BLOCK_NAME.math_display;
    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        // TODO
        return null;
    }
}

export class CoqBlock implements Block {
    public type = BLOCK_NAME.coq;
    constructor( public stringContent: string, public range: BlockRange ) {};

    toProseMirror() {
        // TODO
        return null;
    }
}