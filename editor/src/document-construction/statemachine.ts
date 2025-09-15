import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

enum ParserState {
    /** Parsing regular markdown content */ 
    Markdown,
    /** Parsing the contents of a code block ` ```langid ` to ` ``` ` */
    Code,
    /** Inside a LaTeX block (i.e. $$ ... $$) */
    LaTeX,
    /**  Parsing a hint title (i.e. after `<hint title="` until `"`) */
    HintTitle,
};

enum NestedState {
    /** Not in a hint or an input area */
    None,
    /** Parsing as part of a hint */
    Hint,
    /** Parsing as part of an input area */
    Input,
}

/**
 * Parser for markdown documents.
 * 
 * Next to the regular markdown and code parts this parser has predefined 'tags' for hints and input areas: 
 * * The content between `<hint title="{title}">` and ` </hint>` is turned into a hint cell, `{title}` will turn into the title that is displayed in the editor.
 * * The content between `<input-area>` and `</input-area>` is turned into an input area.
 * @param document The document to convert into a `WaterproofDocument`
 * @param language The language tag to use for the code cells. That is, the part of the ` ``` ` when opening a code block (` ```python ` for a python 
 * code block). Defaults to `""`.
 * @returns A array of `Block` that form a `WaterproofDocument`.
 */
export function markdownParser(document: string, language: string = ""): WaterproofDocument {
    // Stack to store the produced blocks
    const blocks: Block[] = [];

    // Whether we are in a nested state, initially set to none.
    let nested: NestedState = NestedState.None;

    let innerBlocks: Block[] = []
    let state: ParserState = ParserState.Markdown;
    let rangeStart = 0; // Range of the entire block
    let innerRangeStart = 0; // Range of the content

    let rangeStartNested = 0;
    let innerRangeStartNested = 0;

    let hintTitle = "";

    let i = 0;

    // Stores the offset of a codeblock (1 if we have an extra \n, 0 otherwise)
    let codeBlockOffset = 0;

    // Define the tags and their length.
    const hintOpen = '<hint title="', hintOpenLength = hintOpen.length;
    const hintClose = '</hint>', hintCloseLength = hintClose.length;
    const inputAreaOpen = '<input-area>', inputAreaOpenLength = inputAreaOpen.length;
    const inputAreaClose = '</input-area>', inputAreaCloseLength = inputAreaClose.length;
    const codeBlockOpen = '```' + language + "\n", codeBlockOpenLength = codeBlockOpen.length;
    const codeBlockClose = '\n```', codeBlockCloseLength = codeBlockClose.length;
    const latexBlockOpenClose = '$$', latexBlockOpenCloseLength = latexBlockOpenClose.length;

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

    function getRangeStart(): number {
        return nested === NestedState.None ? rangeStart : rangeStartNested;
    }

    function getInnerRangeStart(): number {
        return nested === NestedState.None ? innerRangeStart : innerRangeStartNested;
    }


    function lookAhead(str: string): boolean {
        // return document[i] === str[0] && document.slice(i, i + str.length) === str;
        return document.slice(i, i + str.length) === str;
    }

    function opensCodeBlock(): boolean {
        // Check for both ```lang and \n```lang
        if (lookAhead('\n' + codeBlockOpen)) {
            codeBlockOffset = 1;
            return true;
        } else if (lookAhead(codeBlockOpen)) {
            codeBlockOffset = 0;
            return true;
        }
        return false;
        // return lookAhead(codeBlockOpen) || lookAhead('\n' + codeBlockOpen);
    }

    function opensHintBlock(): boolean {
        return lookAhead(hintOpen);
    }

    function opensInputAreaBlock(): boolean {
        return lookAhead(inputAreaOpen);
    }

    function opensLaTeXBlock(): boolean {
        return lookAhead(latexBlockOpenClose);
    }

    function closesCodeBlock(): boolean {
        // Check for both \n``` and \n```\n
        if (lookAhead(codeBlockClose + '\n')) {
            codeBlockOffset = 1;
            return true;
        } else if (lookAhead(codeBlockClose)) {
            codeBlockOffset = 0;
            return true;
        }
        return false;
        // return lookAhead(codeBlockClose) || lookAhead(codeBlockClose + '\n');
    }

    function closesHintBlock(): boolean {
        return lookAhead(hintClose);
    }

    function closesInputAreaBlock(): boolean {
        return lookAhead(inputAreaClose);
    }

    function closesLaTeXBlock(): boolean {
        return lookAhead(latexBlockOpenClose);
    }

    function backToMarkdown(clearNestedBlocks: boolean = false) {
        state = ParserState.Markdown;
        setRangeStart();
        setInnerRangeStart();
        if (clearNestedBlocks) {
            innerBlocks = [];
        }
    }

    function closeMarkdown() {
        // If there is content in the buffer range then we create a markdown block
        if (i > getRangeStart()) {
            const range = { from: getRangeStart(), to: i };
            const markdownBlock = new MarkdownBlock(
                document.slice(getRangeStart(), i),
                range, range);
            pushBlock(markdownBlock);
        }
    }

    while (i < document.length) {
        switch (state) {
            case ParserState.Markdown: {
                if (opensCodeBlock()) {
                    closeMarkdown();
                    // Set parser state to start parsing the code block contents.
                    state = ParserState.Code;
                    setRangeStart();
                    i += codeBlockOffset + codeBlockOpenLength;
                    setInnerRangeStart();
                    continue;
                }
                else if (opensLaTeXBlock()) {
                    closeMarkdown();
                    state = ParserState.LaTeX;
                    setRangeStart();
                    i += latexBlockOpenCloseLength; // Skip the $$
                    setInnerRangeStart();
                    continue;
                }
                else if (nested === NestedState.None && opensHintBlock()) {
                    closeMarkdown();
                    setRangeStart();
                    i += hintOpenLength; // Skip the <hint title="
                    innerRangeStartNested = i;
                    rangeStartNested = i;
                    state = ParserState.HintTitle;
                    nested = NestedState.Hint;
                    continue;
                }
                else if (nested === NestedState.None && opensInputAreaBlock()) {
                    closeMarkdown();
                    setRangeStart();
                    i += inputAreaOpenLength;
                    setInnerRangeStart();

                    innerRangeStartNested = i;
                    rangeStartNested = i;
                    nested = NestedState.Input;
                    continue;
                }
                else if (nested === NestedState.Hint && closesHintBlock()) {
                    closeMarkdown();
                    
                    nested = NestedState.None;
                    const range = { from: getRangeStart(), to: i + hintCloseLength };
                    const innerRange = { from: getInnerRangeStart(), to: i };
                    const hintBlock = new HintBlock(
                        document.slice(innerRange.from, innerRange.to),
                        hintTitle,
                        range, innerRange,
                        innerBlocks);
                    pushBlock(hintBlock);

                    i += hintCloseLength; // Skip the </hint>
                    backToMarkdown(true);
                    hintTitle = "";
                    continue;
                }
                else if (nested === NestedState.Input && closesInputAreaBlock()) {
                    closeMarkdown();
                    nested = NestedState.None;

                    const range = { from: getRangeStart(), to: i + inputAreaCloseLength };
                    const innerRange = { from: getInnerRangeStart(), to: i};
                    const inputAreaBlock = new InputAreaBlock(
                        document.slice(innerRange.from, innerRange.to),
                        range, innerRange,
                        innerBlocks);
                    pushBlock(inputAreaBlock);

                    i += inputAreaCloseLength; // Skip the </input-area>
                    backToMarkdown(true);
                    continue;
                }
                else {
                    i++;
                    continue;
                }
            }
            case ParserState.Code: {
                if (closesCodeBlock()) {
                    // End of this code block
                    const range = { from: getRangeStart(), to: i + codeBlockCloseLength + codeBlockOffset };
                    const innerRange = { from: getInnerRangeStart(), to: i };
                    const codeBlock = new CodeBlock(
                        document.slice(innerRange.from, innerRange.to),
                        document[rangeStart - 1] === '\n' ? "\n" : "", // prePreWhite
                        "\n", // prePostWhite
                        "\n", // postPreWhite
                        codeBlockOffset === 1 ? "\n" : "", // postPostWhite
                        range,
                        innerRange);
                    pushBlock(codeBlock);
                    i += codeBlockCloseLength + codeBlockOffset; // Skip the closing ```
                    backToMarkdown();
                    continue;
                } else {
                    i++;
                    continue;
                }
            }
            case ParserState.LaTeX: {
                if (closesLaTeXBlock()) {
                    // End of this LaTeX block
                    const range = { from: getRangeStart(), to: i + latexBlockOpenCloseLength };
                    const innerRange = { from: getInnerRangeStart(), to: i };
                    const mathBlock = new MathDisplayBlock(
                        document.slice(getInnerRangeStart(), i),
                        range,
                        innerRange);
                    pushBlock(mathBlock);
                    i += latexBlockOpenCloseLength; // Skip the closing $$
                    backToMarkdown();
                    continue;
                } else {
                    i++;
                    continue;
                }
            }
            case ParserState.HintTitle: {
                // Parse until we find the closing quote and >
                while (i < document.length) {
                    const char = document[i];
                    if (char === '"' && document[i + 1] === '>') {
                        i += 2; // Skip the closing quote and >
                        // Back to parsing markdown
                        backToMarkdown();
                        // The inner range of the hint starts here.
                        innerRangeStart = i;
                        break;
                    } else {
                        hintTitle += char;
                        i++;
                    }
                }
                break;
            }
        }
    }

    // If there is still content then we should create a final markdown block.
    closeMarkdown();
    return blocks;

}