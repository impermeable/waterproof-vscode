import { BLOCK_NAME, Block } from "./block";
import { HintBlock, InputAreaBlock } from "./blocktypes";

export const isInputAreaBlock = (block: Block): block is InputAreaBlock => block.type === BLOCK_NAME.input_area;
export const isHintBlock = (block: Block): block is HintBlock => block.type === BLOCK_NAME.hint;
