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

export const parseDoc2 = (document: string) => parseDocument2(document, "coq");

export function parseDocument2(document: string, language: string): WaterproofDocument {
    const blocks: Block[] = [];

    let nested: NestedState = NestedState.None;

    let innerBlocks: Block[] = []
    let state: ParserState = ParserState.Markdown;
    let rangeStart = 0; // Range of the entire block
    let innerRangeStart = 0; // Range of the content

    let rangeStartNested = 0;
    let innerRangeStartNested = 0;

    let hintTitle = "";

    let i = 0;

    let codeBlockOffset = 0;

    const hintOpen = '<hint title="';
    const hintClose = '</hint>';
    const inputAreaOpen = '<input-area>';
    const inputAreaClose = '</input-area>';
    const codeBlockOpen = '```' + language + "\n";
    const codeBlockClose = '\n```';
    const latexBlockOpenClose = '$$';

    function pushBlock(block: Block) {
        if (nested === NestedState.None) {
            blocks.push(block);
        } else {
            innerBlocks.push(block);
        }
    }

    function setRangeStart(range: number) {
        if (nested === NestedState.None) {
            rangeStart = range;
        } else {
            rangeStartNested = range;
        }
    }

    function setInnerRangeStart(range: number) {
        if (nested === NestedState.None) {
            innerRangeStart = range;
        } else {
            innerRangeStartNested = range;
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

    function backToMarkdown(fromNested: boolean = false) {
        state = ParserState.Markdown;
        setRangeStart(i);
        setInnerRangeStart(i);
        if (fromNested) {
            innerBlocks = [];
        }
    }

    function closeMarkdown() {
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
                    // We have encountered the beginning of a code block. 
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    state = ParserState.Code;
                    setRangeStart(i);
                    i += codeBlockOffset + codeBlockOpen.length;
                    setInnerRangeStart(i);
                    continue;
                }
                else if (opensLaTeXBlock()) {
                    // We have encountered the beginning of a LaTeX block. 
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    state = ParserState.LaTeX;
                    setRangeStart(i);
                    i += latexBlockOpenClose.length; // Skip the $$
                    setInnerRangeStart(i);
                    continue;
                }
                else if (nested === NestedState.None && opensHintBlock()) {
                    // We have encountered the beginning of a hint block.
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    setRangeStart(i);
                    i += hintOpen.length; // Skip the <hint title="
                    innerRangeStartNested = i;
                    rangeStartNested = i;
                    state = ParserState.HintTitle;
                    nested = NestedState.Hint;
                    continue; // Skip the state update at the end of the loop  
                }
                else if (nested === NestedState.None && opensInputAreaBlock()) {
                    // We have encountered the beginning of an input area block.
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    setRangeStart(i);
                    i += inputAreaOpen.length; // Skip the <input-area>
                    setInnerRangeStart(i);

                    innerRangeStartNested = i;
                    rangeStartNested = i;
                    nested = NestedState.Input;
                    continue; // Skip the state update at the end of the loop
                }
                else if (nested === NestedState.Hint && closesHintBlock()) {
                    // We have encountered the end of a hint block.
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    
                    nested = NestedState.None;
                    const range = { from: getRangeStart(), to: i + hintClose.length };
                    const innerRange = { from: getInnerRangeStart(), to: i };
                    const hintBlock = new HintBlock(
                        document.slice(innerRange.from, innerRange.to),
                        hintTitle,
                        range, innerRange,
                        innerBlocks);
                    pushBlock(hintBlock);

                    i += hintClose.length; // Skip the </hint>
                    backToMarkdown(true);
                    hintTitle = "";
                    continue;
                }
                else if (nested === NestedState.Input && closesInputAreaBlock()) {
                    // We have encountered the end of an input area block.
                    // Close off the current markdown block if it has content
                    closeMarkdown();
                    nested = NestedState.None;

                    const range = { from: getRangeStart(), to: i + inputAreaClose.length };
                    const innerRange = { from: getInnerRangeStart(), to: i};
                    const inputAreaBlock = new InputAreaBlock(
                        document.slice(innerRange.from, innerRange.to),
                        range, innerRange,
                        innerBlocks);
                    pushBlock(inputAreaBlock);

                    i += inputAreaClose.length; // Skip the </input-area>
                    backToMarkdown(true);
                    continue;
                }
                else {
                    i++;
                    continue;
                }
                break;   
            }
            case ParserState.Code: {
                if (closesCodeBlock()) {
                    // End of this code block
                    // i now points to the \n of \n``` or \n```\n
                    // console.log("i", i, "document up to i", document.slice(0, i + close), codeBlockOffset);
                    const range = { from: getRangeStart(), to: i + codeBlockClose.length + codeBlockOffset };
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
                    i += codeBlockClose.length + codeBlockOffset; // Skip the closing ```
                    backToMarkdown();
                    continue;
                } else {
                    i++;
                    continue;
                }
                break;
            }
            case ParserState.LaTeX: {
                if (closesLaTeXBlock()) {
                    // End of this LaTeX block
                    const range = { from: getRangeStart(), to: i + latexBlockOpenClose.length };
                    const innerRange = { from: getInnerRangeStart(), to: i };
                    const mathBlock = new MathDisplayBlock(
                        document.slice(getInnerRangeStart(), i),
                        range,
                        innerRange);
                    pushBlock(mathBlock);
                    i += latexBlockOpenClose.length; // Skip the closing $$
                    backToMarkdown();
                } else {
                    i++;
                }
                break;
            }
            case ParserState.HintTitle: {
                // Parse until we find the closing quote and >
                let accHintTitle = "";
                while (i < document.length) {
                    const char = document[i];
                    if (char === '"' && document[i + 1] === '>') {
                        i += 2; // Skip the closing quote and >
                        hintTitle = accHintTitle;
                        backToMarkdown();
                        innerRangeStart = i;
                        break;
                    } else {
                        accHintTitle += char;
                        i++;
                    }
                }
                break;
            }
        }
    }

    closeMarkdown();
    return blocks;

}