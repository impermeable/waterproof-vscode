import { TheSchema } from "../../kroqed-schema";
import { sortBlocks } from "../block-helpers";
import { Block, CoqdownBlock, MathDisplayBlock } from "../blocks";
import { translateCoqDoc } from "../coqdoc-helpers";
import { text } from "../pm-node-constructors";

const regexMathDisplay = /\$([\S\s]*?)\$/g;

// TODO: This macro should be moved to a shared location, since document-constructor.ts also uses it.
const macro = (input, f) => input.slice(1).map((v, i) => f(input.slice(i, i + 2)));

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

    let ranges = macro(mathDisplayBlocks, (blocks: Block[]) => {
        const [blockA, blockB] = blocks;
        return {from: blockA.range.to, to: blockB.range.from};
    });

    // Add first range if it exists
    if (mathDisplayBlocks.length > 0 && mathDisplayBlocks[0].range.from > 0) ranges = [{from: 0, to: mathDisplayBlocks[0].range.from}, ...ranges];
    // Add last range if it exists
    if (mathDisplayBlocks.length > 0 && mathDisplayBlocks[mathDisplayBlocks.length - 1].range.to < coqdocComment.length) ranges = [...ranges, {from: mathDisplayBlocks[mathDisplayBlocks.length - 1].range.to, to: coqdocComment.length}];

    // populate the ranges with coqdown blocks. 
    const blocks = sortBlocks([...mathDisplayBlocks, ...createCoqDownBlocks(coqdocComment, ranges)]);

    return blocks;
}

// TODO: Maybe move?
export function createCoqDownBlocks(inputComment: string, ranges: {from: number, to: number}[]) {
    const markdownBlocks = ranges.map((range) => {
        const content = inputComment.slice(range.from, range.to);
        // TODO: Should we translate here? Or does it translate somewhere else? 
        return new CoqdownBlock(translateCoqDoc(content), range);
    });
    return markdownBlocks;
}