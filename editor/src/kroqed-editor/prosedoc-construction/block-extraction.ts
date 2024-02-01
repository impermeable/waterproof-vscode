import { HintBlock, InputAreaBlock } from "./blocks";

const regexes = {
    coq: /```coq\n([\s\S]*?)\n```/g,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>\n([\s\S]*?)\n<\/input-area>/g,
    hint: /<hint title="([\s\S]*?)">\n([\s\S]*?)\n<\/hint>/g
}

/**
 * Create input blocks from document string. 
 * 
 * Uses regexes to search for `<input-area>` and `</input-area>` tags.
 */
export function createInputBlocks(document: string) {
    const input_areas = document.matchAll(regexes.input_area);

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        return new InputAreaBlock(input_area[1], range);
    });

    return inputAreaBlocks;
}

/**
 * Create hint blocks from document string. 
 * 
 * Uses regexes to search for `<hint>` and `</hint>` tags.
 */
export function createHintBlocks(document: string) {
    const hints = document.matchAll(regexes.hint);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const range = { from: hint.index, to: hint.index + hint[0].length };
        return new HintBlock(hint[2], hint[1], range);
    });

    return hintBlocks;
}