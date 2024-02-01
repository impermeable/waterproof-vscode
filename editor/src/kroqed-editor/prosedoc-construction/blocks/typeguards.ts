import { BLOCK_NAME, Block } from "./block";
import { CoqBlock, HintBlock, InputAreaBlock, MathDisplayBlock } from "./blocktypes";

export const isInputAreaBlock = (block: Block): block is InputAreaBlock => block.type === BLOCK_NAME.input_area;
export const isHintBlock = (block: Block): block is HintBlock => block.type === BLOCK_NAME.hint;
export const isMathDisplayBlock = (block: Block): block is MathDisplayBlock => block.type === BLOCK_NAME.math_display;
export const isCoqBlock = (block: Block): block is CoqBlock => block.type === BLOCK_NAME.coq;