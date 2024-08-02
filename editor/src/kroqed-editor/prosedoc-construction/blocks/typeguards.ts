import { BLOCK_NAME, Block } from "./block";
import { CoqBlock, CoqCodeBlock, CoqDocBlock, CoqMarkdownBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock } from "./blocktypes";

export const isInputAreaBlock = (block: Block): block is InputAreaBlock => block.type === BLOCK_NAME.INPUT_AREA;
export const isHintBlock = (block: Block): block is HintBlock => block.type === BLOCK_NAME.HINT;
export const isMathDisplayBlock = (block: Block): block is MathDisplayBlock => block.type === BLOCK_NAME.MATH_DISPLAY;
export const isCoqBlock = (block: Block): block is CoqBlock => block.type === BLOCK_NAME.COQ;
export const isMarkdownBlock = (block: Block): block is MarkdownBlock => block.type === BLOCK_NAME.MARKDOWN;
export const isCoqMarkdownBlock = (block: Block): block is CoqMarkdownBlock => block.type === BLOCK_NAME.COQ_MARKDOWN;
export const isCoqDocBlock = (block: Block): block is CoqDocBlock => block.type === BLOCK_NAME.COQ_DOC;
export const isCoqCodeBlock = (block: Block): block is CoqCodeBlock => block.type === BLOCK_NAME.COQ_CODE;