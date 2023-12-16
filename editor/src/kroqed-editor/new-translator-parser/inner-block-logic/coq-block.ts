import { TheSchema } from "../../kroqed-schema";
import { sortBlocks } from "../block-helpers";
import { Block, CoqdownBlock, MathDisplayBlock } from "../blocks";
import { translateCoqDoc } from "../coqdoc-helpers";
import { text } from "../pm-node-constructors";
import { extractInterBlockRanges } from "../utils";

const regexMathDisplay = /\$([\S\s]*?)\$/g;

/**
 * Parses a coqdoc block.
 * @param coqdocComment 
 */
export function createCoqDoc(coqdocComment: string) {
    // coqdoc contains math_display and coqdown nodes.
    
    const mathDisplays = coqdocComment.matchAll(regexMathDisplay);
    
    // TODO: MOve to helper functions.
    const mathDisplayBlocks = sortBlocks(Array.from(mathDisplays).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length };
        return new MathDisplayBlock(math[1], range);
    }));

    const ranges = extractInterBlockRanges(mathDisplayBlocks, coqdocComment);

    // populate the ranges with coqdown blocks. 
    const blocks = sortBlocks([...mathDisplayBlocks, ...createCoqDownBlocks(coqdocComment, ranges)]);

    return blocks;
}

// TODO: Maybe move?
export function createCoqDownBlocks(inputComment: string, ranges: {from: number, to: number}[]) {
    const markdownBlocks = ranges.map((range) => {
        const content = inputComment.slice(range.from, range.to);
        // TODO: Should we translate here? Or does it translate somewhere else? 
        return new CoqdownBlock(content, range);
    });
    return markdownBlocks;
}