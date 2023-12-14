import { CoqBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock } from "./blocks";

const regexes = {
    coq: /```coq\n([\s\S]*?)\n```/g,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>\n([\s\S]*?)\n<\/input-area>/g,
    hint: /<hint title="([\s\S]*?)">\n([\s\S]*?)\n<\/hint>/g
}

export function createInputBlocks(document: string) {
    const input_areas = document.matchAll(regexes.input_area);

    const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
        if (input_area.index === undefined) throw new Error("Index of input_area is undefined");
        const range = { from: input_area.index, to: input_area.index + input_area[0].length };
        return new InputAreaBlock(input_area[1], range);
    });

    return inputAreaBlocks;
}

export function createHintBlocks(document: string) {
    const hints = document.matchAll(regexes.hint);

    const hintBlocks = Array.from(hints).map((hint) => {
        if (hint.index === undefined) throw new Error("Index of hint is undefined");
        const range = { from: hint.index, to: hint.index + hint[0].length };
        return new HintBlock(hint[2], hint[1], range);
    });

    return hintBlocks;
}

export function createMathDisplayBlocks(inputDocument: string) {
    const math_display = inputDocument.matchAll(regexes.math_display);
    const mathDisplayBlocks = Array.from(math_display).map((math) => {
        if (math.index === undefined) throw new Error("Index of math is undefined");
        const range = { from: math.index, to: math.index + math[0].length };
        return new MathDisplayBlock(math[1], range);
    });
    return mathDisplayBlocks;
}

export function createCoqBlocks(inputDocument: string) {
    const coq_code = inputDocument.matchAll(regexes.coq);
    const coqBlocks = Array.from(coq_code).map((coq) => {
        if (coq.index === undefined) throw new Error("Index of coq is undefined");
        const range = { from: coq.index, to: coq.index + coq[0].length };
        return new CoqBlock(coq[1], range);
    });
    return coqBlocks;
}


export function createMarkdownBlocks(inputDocument: string, ranges: {from: number, to: number}[]) {
    const markdownBlocks = ranges.map((range) => {
        const content = inputDocument.slice(range.from, range.to);
        return new MarkdownBlock(content, range);
    });
    return markdownBlocks;
}

