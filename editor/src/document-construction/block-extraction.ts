import {
  InputAreaBlock,
  HintBlock,
  MathDisplayBlock,
  CodeBlock,
  NewlineBlock,
} from "@impermeable/waterproof-editor";
import { createInputAndHintInnerBlocks } from "./inner-blocks";

const regexes = {
  // coq: /```coq\n([\s\S]*?)\n```/g,
  coq: /(\n)?^```coq\n([^]*?)\n?^```$(\n)?/gm,
  math_display: /\$\$([\s\S]*?)\$\$/g,
  input_area: /<input-area>([\s\S]*?)<\/input-area>/g,
  input_areaV: /\(\* begin input \*\)\n([\s\S]*?)\n\(\* end input \*\)/gm,
  hint: /<hint title="([\s\S]*?)">([\s\S]*?)<\/hint>/g,
  hintV: /\(\* begin hint : ([\s\S]*?) \*\)\n([\s\S]*?)\n\(\* end hint \*\)/gm,
};

/**
 * Create input blocks from document string.
 *
 * Uses regexes to search for
 * - `<input-area>` and `</input-area>` tags (mv files)
 * - `(* begin input *)` and `(* end input *)` (v files)
 */
export function extractInputBlocks(document: string) {
  return extractInputBlocksMV(document);
}

const inputAreaTagOpenLength = "<input-area>".length;
const inputAreaTagCloseLength = "</input-area>".length;

function extractInputBlocksMV(document: string) {
  const input_areas = document.matchAll(regexes.input_area);

  const inputAreaBlocks = Array.from(input_areas).map((input_area) => {
    if (input_area.index === undefined)
      throw new Error("Index of input_area is undefined");
    const range = {
      from: input_area.index,
      to: input_area.index + input_area[0].length,
    };
    const innerRange = {
      from: range.from + inputAreaTagOpenLength,
      to: range.to - inputAreaTagCloseLength,
    };
    return new InputAreaBlock(
      input_area[1],
      range,
      innerRange,
      0,
      createInputAndHintInnerBlocks(input_area[1], innerRange),
    );
  });

  return inputAreaBlocks;
}

/**
 * Create hint blocks from document string.
 *
 * Uses regexes to search for
 * - `<hint title=[hint title]>` and `</hint>` tags (mv files)
 * - `(* begin hint : [hint title] *)` and `(* end hint *)` (v files)
 */
export function extractHintBlocks(document: string): HintBlock[] {
  return extractHintBlocksMV(document);
}

const hintTagOpenLength = '<hint title="">'.length;
const hintTagCloseLength = "</hint>".length;

function extractHintBlocksMV(document: string) {
  const hints = document.matchAll(regexes.hint);

  const hintBlocks = Array.from(hints).map((hint) => {
    if (hint.index === undefined) throw new Error("Index of hint is undefined");
    const title = hint[1];
    const range = { from: hint.index, to: hint.index + hint[0].length };
    const innerRange = {
      from: range.from + hintTagOpenLength + title.length,
      to: range.to - hintTagCloseLength,
    };
    return new HintBlock(
      hint[2],
      title,
      range,
      innerRange,
      0,
      createInputAndHintInnerBlocks(hint[2], innerRange),
    );
  });

  return hintBlocks;
}

/**
 * Create math display blocks from document string.
 *
 * Uses regexes to search for `$$`.
 */
export function extractMathDisplayBlocks(
  inputDocument: string,
  parentOffset: number = 0,
) {
  const math_display = inputDocument.matchAll(regexes.math_display);
  const mathDisplayBlocks = Array.from(math_display).map((math) => {
    if (math.index === undefined) throw new Error("Index of math is undefined");
    const range = {
      from: math.index + parentOffset,
      to: math.index + math[0].length + parentOffset,
    };
    const innerRange = {
      from: range.from + "$$".length,
      to: range.to - "$$".length,
    };
    return new MathDisplayBlock(math[1], range, innerRange, 0);
  });
  return mathDisplayBlocks;
}

const rocqOpenLength = "```coq\n".length;
const rocqCloseLength = "\n```".length;

/**
 * Create rocq blocks from document string.
 *
 * Uses regexes to search for ` ```coq ` and ` ```  ` markers.
 */
export function extractRocqBlocks(
  inputDocument: string,
  parentOffset: number = 0,
): Array<CodeBlock | NewlineBlock> {
  const rocq_code = Array.from(inputDocument.matchAll(regexes.coq));

  const blocks = rocq_code.flatMap((rocq) => {
    if (rocq.index === undefined) throw new Error("Index of rocq is undefined");

    // - rocq[0] the match;
    // - rocq[1] capture group 1, newline before the ```coq (if any);
    // - rocq[2] ..., the content of the rocq block;
    // - rocq[3] ..., newline after the ``` (if any).
    // console.log(`==========\nprePreWhite: '${rocq[1] == "\n"}'\nprePostWhite: '${rocq[2] == "\n"}'\ncontent: '${rocq[3]}'\npostPreWhite: '${rocq[4] == "\n"}'\npostPostWhite: '${rocq[5] == "\n"}'\n==========\n`)
    const content = rocq[2];
    const newlineBefore = rocq[1] == "\n";
    const newlineAfter = rocq[3] == "\n";

    // Range of the whole rocq block including the ```coq and ``` markers, but without the newlines before/after if any.
    const range = {
      from: rocq.index + parentOffset + (newlineBefore ? 1 : 0),
      to:
        rocq.index +
        parentOffset +
        (newlineBefore ? 1 : 0) +
        rocq[2].length +
        rocqOpenLength +
        rocqCloseLength,
    };

    // Range of the inner content of the rocq block, excluding the ```coq and ``` markers.
    const innerRange = {
      from: range.from + rocqOpenLength,
      to: range.to - rocqCloseLength,
    };

    const rocqBlock = new CodeBlock(content, range, innerRange, 0);

    if (newlineBefore && !newlineAfter) {
      return [
        new NewlineBlock(
          {
            from: rocq.index + parentOffset,
            to: rocq.index + 1 + parentOffset,
          },
          {
            from: rocq.index + parentOffset,
            to: rocq.index + 1 + parentOffset,
          },
          0,
        ),
        rocqBlock,
      ];
    } else if (!newlineBefore && newlineAfter) {
      return [
        rocqBlock,
        new NewlineBlock(
          { from: range.to, to: range.to + 1 },
          { from: range.to, to: range.to + 1 },
          0,
        ),
      ];
    } else if (newlineBefore && newlineAfter) {
      return [
        new NewlineBlock(
          {
            from: rocq.index + parentOffset,
            to: rocq.index + 1 + parentOffset,
          },
          {
            from: rocq.index + parentOffset,
            to: rocq.index + 1 + parentOffset,
          },
          0,
        ),
        rocqBlock,
        new NewlineBlock(
          { from: range.to, to: range.to + 1 },
          { from: range.to, to: range.to + 1 },
          0,
        ),
      ];
    } else {
      return [rocqBlock];
    }
  });

  return blocks;
}

// Regex for extracting the math display blocks from the rocqdoc comments.
// We need a different regex here, since rocq markdown uses single dollar signs for math display :)
const regexMathDisplay = /\$([\S\s]*?)\$/g;

export function extractMathDisplayBlocksRocqDoc(
  input: string,
): MathDisplayBlock[] {
  const mathDisplay = Array.from(input.matchAll(regexMathDisplay));
  const mathDisplayBlocks = Array.from(mathDisplay).map((math) => {
    if (math.index === undefined) throw new Error("Index of math is undefined");
    const range = { from: math.index, to: math.index + math[0].length };
    const innerRange = {
      from: range.from + "$$".length,
      to: range.to - "$$".length,
    };
    return new MathDisplayBlock(math[1], range, innerRange, 0);
  });
  return mathDisplayBlocks;
}
