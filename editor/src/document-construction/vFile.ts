import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";


enum VParserState {
	/** Parsing regular code content */
	Code,
	/** Parsing a hint title (after begin details : ... until *) */
	HintTitle,
	/** Parsing markdown block ((** ... *)) */
	Markdown,
	/** Parsing math display ($$ ... $$) inside markdown */
	MathDisplay,
}

enum VNestedState {
	None,
	Hint,
	Input,
}

/**
 * Parser for .v (Coq) files.
 * Recognizes code, hint, and input area blocks.
 *
 * - Code is the default state.
 * - Hints: between `(* begin details : title *)` and `(* end details *)`.
 * - Input areas: between `(* begin input *)` and `(* end input *)`.
 *
 * @param document The .v file content
 * @returns An array of Block forming a WaterproofDocument
 */
export function vFileParser(document: string): WaterproofDocument {
	const blocks: Block[] = [];
	let nested: VNestedState = VNestedState.None;
	let innerBlocks: Block[] = [];
    // Here state is initialized to Code
	let state: VParserState = VParserState.Code;
	let rangeStart = 0;
	let innerRangeStart = 0;
	let rangeStartNested = 0;
	let innerRangeStartNested = 0;
	let hintTitle = "";
	let i = 0;

	const hintOpen = '(* begin details : ', hintOpenLength = hintOpen.length;
    const hintTitleEnd = ' *)\n', hintTitleEndLength = hintTitleEnd.length;
	const hintClose = '\n(* end details *)', hintCloseLength = hintClose.length;
	const inputOpen = '(* begin input *)\n', inputOpenLength = inputOpen.length;
	const inputClose = '\n(* end input *)', inputCloseLength = inputClose.length;
	const markdownOpen = '(** ', markdownOpenLength = markdownOpen.length;
	const markdownClose = ' *)', markdownCloseLength = markdownClose.length;
	const mathOpen = '$', mathOpenLength = mathOpen.length;
	const mathClose = '$', mathCloseLength = mathClose.length;


	function pushBlock(block: Block) {
		if (nested === VNestedState.None) {
			blocks.push(block);
		} else {
			innerBlocks.push(block);
		}
	}

	function setRangeStart() {
		if (nested === VNestedState.None) {
			rangeStart = i;
		} else {
			rangeStartNested = i;
		}
	}

	function setInnerRangeStart() {
		if (nested === VNestedState.None) {
			innerRangeStart = i;
		} else {
			innerRangeStartNested = i;
		}
	}

	function getRangeStart(): number {
		return nested === VNestedState.None ? rangeStart : rangeStartNested;
	}

	function getInnerRangeStart(): number {
		return nested === VNestedState.None ? innerRangeStart : innerRangeStartNested;
	}

	function lookAhead(str: string): boolean {
		return document.slice(i, i + str.length) === str;
	}

	function opensHintBlock(): boolean {
		return lookAhead(hintOpen);
	}
	function closesHintBlock(): boolean {
		return lookAhead(hintClose);
	}
	function opensInputBlock(): boolean {
		return lookAhead(inputOpen);
	}
	function closesInputBlock(): boolean {
		return lookAhead(inputClose);
	}

	function backToCode(clearNestedBlocks: boolean = false) {
		state = VParserState.Code;
		setRangeStart();
		setInnerRangeStart();
		if (clearNestedBlocks) {
			innerBlocks = [];
		}
	}

	function closeCode() {
		if (i > getRangeStart()) {
			const range = { from: getRangeStart(), to: i };
            const startsWithNewline = document[range.from] === '\n';
            const endsWithNewline = document[range.to - 1] === '\n';
			const codeBlock = new CodeBlock(
				document.slice(range.from + (startsWithNewline ? 1 : 0), range.to - (endsWithNewline ? 1 : 0)),
				startsWithNewline ? "\n" : "\n", "\n", "", endsWithNewline ? "\n" : "",
				range, range
			);
			pushBlock(codeBlock);
		}
	}


	function opensMarkdownBlock(): boolean {
		return lookAhead(markdownOpen);
	}
	function closesMarkdownBlock(): boolean {
		return lookAhead(markdownClose);
	}
	function opensMathBlock(): boolean {
		return lookAhead(mathOpen);
	}
	function closesMathBlock(): boolean {
		return lookAhead(mathClose);
	}

	function closeMarkdown() {
		if (i > getRangeStart()) {
			const range = { from: getRangeStart(), to: i + markdownCloseLength };
            const innerRange = { from: getInnerRangeStart(), to: i };
			const markdownBlock = new MarkdownBlock(
				document.slice(innerRange.from, innerRange.to),
				range, innerRange
			);
			pushBlock(markdownBlock);
		}
	}

	function closeMathDisplay() {
		if (i > getRangeStart()) {
			const range = { from: getRangeStart(), to: i };
			const mathBlock = new MathDisplayBlock(
				document.slice(getRangeStart(), i),
				range, range
			);
			pushBlock(mathBlock);
		}
	}

	while (i < document.length) {
		switch (state) {
			case VParserState.Code: {
				if (opensHintBlock() && nested === VNestedState.None) {
					closeCode();
					setRangeStart();
					i += hintOpenLength;
					state = VParserState.HintTitle;
					nested = VNestedState.Hint;
					hintTitle = "";
					continue;
				} else if (opensInputBlock() && nested === VNestedState.None) {
					closeCode();
					setRangeStart();
					i += inputOpenLength;
					setInnerRangeStart();
					innerRangeStartNested = i;
					rangeStartNested = i;
					nested = VNestedState.Input;
					continue;
				} else if (opensMarkdownBlock()) {
					closeCode();
					setRangeStart();
					i += markdownOpenLength;
					setInnerRangeStart();
					state = VParserState.Markdown;
					continue;
				} else if (nested === VNestedState.Hint && closesHintBlock()) {
					closeCode();
					nested = VNestedState.None;
					const range = { from: getRangeStart(), to: i + hintCloseLength };
					const innerRange = { from: getInnerRangeStart(), to: i };
					const hintBlock = new HintBlock(
						document.slice(innerRange.from, innerRange.to),
						hintTitle.trim(),
						range, innerRange,
						innerBlocks
					);
					pushBlock(hintBlock);
					i += hintCloseLength;
					backToCode(true);
					hintTitle = "";
					continue;
				} else if (nested === VNestedState.Input && closesInputBlock()) {
					closeCode();
					nested = VNestedState.None;
					const range = { from: getRangeStart(), to: i + inputCloseLength };
					const innerRange = { from: getInnerRangeStart(), to: i };
					const inputBlock = new InputAreaBlock(
						document.slice(innerRange.from, innerRange.to),
						range, innerRange,
						innerBlocks
					);
					pushBlock(inputBlock);
					i += inputCloseLength;
					backToCode(true);
					continue;
				} else {
					i++;
					continue;
				}
			}
			case VParserState.Markdown: {
				if (opensMathBlock()) {
					closeMarkdown();
					setRangeStart();
					i += mathOpenLength;
					setInnerRangeStart();
					state = VParserState.MathDisplay;
					continue;
				} else if (closesMarkdownBlock()) {
					closeMarkdown();
					i += markdownCloseLength;
					backToCode();
					continue;
				} else {
					i++;
					continue;
				}
			}
			case VParserState.MathDisplay: {
				if (closesMathBlock()) {
					closeMathDisplay();
					i += mathCloseLength;
					state = VParserState.Markdown;
					setRangeStart();
					setInnerRangeStart();
					continue;
				} else {
					i++;
					continue;
				}
			}
			case VParserState.HintTitle: {
				while (i < document.length) {
					if (lookAhead(hintTitleEnd)) {
						i += hintTitleEndLength;
						backToCode();
						innerRangeStart = i;
						break;
					} else {
						hintTitle += document[i];
						i++;
					}
				}
				break;
			}
		}
	}
	// Final code block
	closeCode();
	return blocks;
}
