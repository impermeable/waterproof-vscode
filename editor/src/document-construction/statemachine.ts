import {
  WaterproofDocument,
  Block,
  MarkdownBlock,
  HintBlock,
  InputAreaBlock,
  StudentHiddenBlock,
  CodeBlock,
  NewlineBlock,
  MathDisplayBlock,
} from "@impermeable/waterproof-editor";

enum ParserState {
  /** Parsing regular markdown content */
  Markdown,
  /** Parsing the contents of a code block ` ```langid ` to ` ``` ` */
  Code,
  /** Inside a LaTeX block (i.e. $$ ... $$) */
  LaTeX,
  /**  Parsing a hint title (i.e. after `<hint title="` until `"`) */
  HintTitle,
}

enum NestedState {
  /** Not in a hint, input area, or student-hidden block */
  None,
  /** Parsing as part of a hint */
  Hint,
  /** Parsing as part of an input area */
  Input,
  /** Parsing as part of a student-hidden block */
  StudentHidden,
}

/**
 * Parser for markdown documents.
 *
 * Next to the regular markdown and code parts this parser has predefined 'tags' for hints, input areas, and student-hidden blocks:
 * * The content between `<hint title="{title}">` and ` </hint>` is turned into a hint cell, `{title}` will turn into the title that is displayed in the editor.
 * * The content between `<input-area>` and `</input-area>` is turned into an input area.
 * * The content between `<student-hidden>` and `</student-hidden>` is turned into a student-hidden block (only visible in teacher mode).
 * @param document The document to convert into a `WaterproofDocument`
 *
 * NOTE: This is a slightly modified version of the markdown parser that is included by default in waterproof-editor.
 * We include a change here that allows us to parse both ```coq and ```rocq at the same time.
 */
export function parse(document: string): WaterproofDocument {
  // Stack to store the produced blocks
  const blocks: Block[] = [];

  // By default (when no language is specified in the config) we use "```", otherwise we prepend the code open ticks
  const languages = ["rocq", "coq"];

  // Whether we are in a nested state, initially set to none.
  let nested: NestedState = NestedState.None;

  let innerBlocks: Block[] = [];
  let state: ParserState = ParserState.Markdown;
  let rangeStart = 0; // Range of the entire block
  let innerRangeStart = 0; // Range of the content

  let rangeStartNested = 0;
  let innerRangeStartNested = 0;
  let lineStartCounter = 0;

  let hintTitle = "";

  let i = 0;
  let newlineCounter = 0;

  // Stores the offset of a codeblock (1 if we have an extra \n, 0 otherwise)
  let codeBlockOffset = 0;

  // Define the tags and their length.
  const hintOpen = '<hint title="',
    hintOpenLength = hintOpen.length;
  const hintClose = "</hint>",
    hintCloseLength = hintClose.length;
  const inputAreaOpen = "<input-area>",
    inputAreaOpenLength = inputAreaOpen.length;
  const inputAreaClose = "</input-area>",
    inputAreaCloseLength = inputAreaClose.length;
  const studentHiddenOpen = "<student-hidden>",
    studentHiddenOpenLength = studentHiddenOpen.length;
  const studentHiddenClose = "</student-hidden>",
    studentHiddenCloseLength = studentHiddenClose.length;
  const codeBlockClose = "\n```",
    codeBlockCloseLength = codeBlockClose.length;
  const latexBlockOpenClose = "$$",
    latexBlockOpenCloseLength = latexBlockOpenClose.length;

  // Push block to the stack.
  function pushBlock(block: Block) {
    // When in nested mode we push to the innerBlock stack, otherwise we push to the block stack
    if (nested === NestedState.None) {
      blocks.push(block);
    } else {
      innerBlocks.push(block);
    }
  }

  function setRangeStart() {
    if (nested === NestedState.None) {
      rangeStart = i;
    } else {
      rangeStartNested = i;
    }
  }

  function setInnerRangeStart() {
    if (nested === NestedState.None) {
      innerRangeStart = i;
    } else {
      innerRangeStartNested = i;
    }
  }

  function setLineStart() {
    lineStartCounter = newlineCounter;
  }

  function getRangeStart(): number {
    return nested === NestedState.None ? rangeStart : rangeStartNested;
  }

  function getInnerRangeStart(): number {
    return nested === NestedState.None
      ? innerRangeStart
      : innerRangeStartNested;
  }

  function getLineStart() {
    return lineStartCounter;
  }

  function lookAhead(str: string, advance: number = 0): boolean {
    return document.slice(i + advance, i + advance + str.length) === str;
  }

  function lookAheadLangIds(advance: number = 0): string | undefined {
    return languages.find(
      (str) => document.slice(i + advance, i + str.length + advance) === str,
    );
  }

  function opensCodeBlock(): number {
    // Check for both ```lang and \n```lang
    const lookAhead4 = lookAheadLangIds(4);
    const lookAhead3 = lookAheadLangIds(3);
    if (
      lookAhead("\n```") &&
      lookAhead4 !== undefined &&
      lookAhead("\n", 4 + lookAhead4.length)
    ) {
      codeBlockOffset = 1;
      return 4 + lookAhead4.length;
    } else if (
      lookAhead("```") &&
      lookAhead3 !== undefined &&
      lookAhead("\n", 3 + lookAhead3.length)
    ) {
      codeBlockOffset = 0;
      return 4 + lookAhead3.length;
    }
    return 0;
  }

  function opensHintBlock(): boolean {
    return lookAhead(hintOpen);
  }

  function opensInputAreaBlock(): boolean {
    return lookAhead(inputAreaOpen);
  }

  function opensStudentHiddenBlock(): boolean {
    return lookAhead(studentHiddenOpen);
  }

  function opensLaTeXBlock(): boolean {
    return lookAhead(latexBlockOpenClose);
  }

  function closesCodeBlock(): boolean {
    // Check for both \n``` and \n```\n
    if (lookAhead(codeBlockClose + "\n")) {
      codeBlockOffset = 1;
      return true;
    } else if (lookAhead(codeBlockClose)) {
      codeBlockOffset = 0;
      return true;
    }
    return false;
  }

  function closesHintBlock(): boolean {
    return lookAhead(hintClose);
  }

  function closesInputAreaBlock(): boolean {
    return lookAhead(inputAreaClose);
  }

  function closesStudentHiddenBlock(): boolean {
    return lookAhead(studentHiddenClose);
  }

  function closesLaTeXBlock(): boolean {
    return lookAhead(latexBlockOpenClose);
  }

  function backToMarkdown(clearNestedBlocks: boolean = false) {
    state = ParserState.Markdown;
    setRangeStart();
    setInnerRangeStart();
    setLineStart();
    if (clearNestedBlocks) {
      innerBlocks = [];
    }
  }

  function closeMarkdown() {
    // If there is content in the buffer range then we create a markdown block
    if (i > getRangeStart()) {
      const from = getRangeStart();
      const to = i;
      const markdownBlock = new MarkdownBlock(
        document.slice(getRangeStart(), i),
        { from, to },
        { from, to },
        0,
      );
      pushBlock(markdownBlock);
    }
  }

  function checkNewlineAndIncrementI(): void {
    if (document[i] === "\n") newlineCounter++;
    i++;
  }

  function handleMarkdownCase(): void {
    const codeBlockOpenLength = opensCodeBlock();
    // opensCodeBlock returns the length (> 0) of the opening tag
    // when the next part opens a code block.
    if (codeBlockOpenLength) {
      closeMarkdown();
      // Set parser state to start parsing the code block contents.
      state = ParserState.Code;
      setRangeStart();
      i += codeBlockOffset + codeBlockOpenLength;
      newlineCounter += codeBlockOffset;
      newlineCounter++;
      setInnerRangeStart();
      setLineStart();
    } else if (opensLaTeXBlock()) {
      closeMarkdown();
      state = ParserState.LaTeX;
      setRangeStart();
      i += latexBlockOpenCloseLength; // Skip the $$
      setInnerRangeStart();
      setLineStart();
    } else if (nested === NestedState.None && opensHintBlock()) {
      closeMarkdown();
      setRangeStart();
      setLineStart();
      i += hintOpenLength; // Skip the <hint title="
      innerRangeStartNested = i;
      rangeStartNested = i;
      state = ParserState.HintTitle;
      nested = NestedState.Hint;
    } else if (nested === NestedState.None && opensInputAreaBlock()) {
      closeMarkdown();
      setRangeStart();
      i += inputAreaOpenLength;
      setInnerRangeStart();
      setLineStart();
      innerRangeStartNested = i;
      rangeStartNested = i;
      nested = NestedState.Input;
    } else if (nested === NestedState.None && opensStudentHiddenBlock()) {
      closeMarkdown();
      setRangeStart();
      i += studentHiddenOpenLength;
      setInnerRangeStart();
      setLineStart();
      innerRangeStartNested = i;
      rangeStartNested = i;
      nested = NestedState.StudentHidden;
    } else if (nested === NestedState.Hint && closesHintBlock()) {
      closeMarkdown();
      nested = NestedState.None;
      const range = { from: getRangeStart(), to: i + hintCloseLength };
      const innerRange = { from: getInnerRangeStart(), to: i };
      const hintBlock = new HintBlock(
        document.slice(innerRange.from, innerRange.to),
        hintTitle,
        range,
        innerRange,
        0,
        innerBlocks,
      );
      pushBlock(hintBlock);
      i += hintCloseLength; // Skip the </hint>
      backToMarkdown(true);
      hintTitle = "";
    } else if (nested === NestedState.Input && closesInputAreaBlock()) {
      closeMarkdown();
      nested = NestedState.None;
      const range = { from: getRangeStart(), to: i + inputAreaCloseLength };
      const innerRange = { from: getInnerRangeStart(), to: i };
      const inputAreaBlock = new InputAreaBlock(
        document.slice(innerRange.from, innerRange.to),
        range,
        innerRange,
        0,
        innerBlocks,
      );
      pushBlock(inputAreaBlock);
      i += inputAreaCloseLength; // Skip the </input-area>
      backToMarkdown(true);
    } else if (
      nested === NestedState.StudentHidden &&
      closesStudentHiddenBlock()
    ) {
      closeMarkdown();
      nested = NestedState.None;
      const range = { from: getRangeStart(), to: i + studentHiddenCloseLength };
      const innerRange = { from: getInnerRangeStart(), to: i };
      const studentHiddenBlock = new StudentHiddenBlock(
        document.slice(innerRange.from, innerRange.to),
        range,
        innerRange,
        0,
        innerBlocks,
      );
      pushBlock(studentHiddenBlock);
      i += studentHiddenCloseLength; // Skip the </student-hidden>
      backToMarkdown(true);
    } else {
      checkNewlineAndIncrementI();
    }
  }

  function handleCodeCase(): void {
    if (closesCodeBlock()) {
      // End of this code block
      newlineCounter++;

      // Check if we have a newline before this block
      const newlineBefore = document[getRangeStart()] === "\n";
      const range = {
        from: getRangeStart() + (newlineBefore ? 1 : 0),
        to: i + codeBlockCloseLength,
      };
      const innerRange = { from: getInnerRangeStart(), to: i };
      const codeBlock = new CodeBlock(
        document.slice(innerRange.from, innerRange.to),
        range,
        innerRange,
        getLineStart(),
      );

      // Add a newline block before the block if needed
      if (newlineBefore) {
        pushBlock(
          new NewlineBlock(
            { from: getRangeStart(), to: getRangeStart() + 1 },
            { from: getRangeStart(), to: getRangeStart() + 1 },
            0,
          ),
        );
      }
      pushBlock(codeBlock);
      // Add a newline block after the block if needed
      if (codeBlockOffset) {
        newlineCounter++;
        pushBlock(
          new NewlineBlock(
            { from: range.to, to: range.to + 1 },
            { from: range.to, to: range.to + 1 },
            0,
          ),
        );
      }
      i += codeBlockCloseLength + codeBlockOffset; // Skip the closing ``` and possible \n
      backToMarkdown();
    } else {
      checkNewlineAndIncrementI();
    }
  }

  function handleLaTeXCase(): void {
    if (closesLaTeXBlock()) {
      // End of this LaTeX block
      const range = {
        from: getRangeStart(),
        to: i + latexBlockOpenCloseLength,
      };
      const innerRange = { from: getInnerRangeStart(), to: i };
      const mathBlock = new MathDisplayBlock(
        document.slice(getInnerRangeStart(), i),
        range,
        innerRange,
        0,
      );
      pushBlock(mathBlock);
      i += latexBlockOpenCloseLength; // Skip the closing $$
      backToMarkdown();
    } else {
      checkNewlineAndIncrementI();
    }
  }

  function handleHintTitleCase(): void {
    // Parse until we find the closing quote and >
    while (i < document.length) {
      const char = document[i];
      if (char === '"' && document[i + 1] === ">") {
        i += 2; // Skip the closing quote and >
        // Back to parsing markdown
        backToMarkdown();
        // The inner range of the hint starts here.
        innerRangeStart = i;
        break;
      } else {
        hintTitle += char;
        checkNewlineAndIncrementI();
      }
    }
  }

  while (i < document.length) {
    switch (state as ParserState) {
      case ParserState.Markdown:
        handleMarkdownCase();
        break;
      case ParserState.Code:
        handleCodeCase();
        break;
      case ParserState.LaTeX:
        handleLaTeXCase();
        break;
      case ParserState.HintTitle:
        handleHintTitleCase();
        break;
    }
  }

  // If there is still content then we should create a final markdown block.
  closeMarkdown();
  return blocks;
}
