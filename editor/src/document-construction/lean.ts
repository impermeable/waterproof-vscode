import { Block, BlockRange, CodeBlock, ContainerBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, NewlineBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

enum Kind {
    Text,
    Preamble,
    CodeOpen,
    CodeClose,
    InputOpen,
    HintOpen,
    Close,
    MathInline,
    MathDisplay,
    Newline,
    MultileanOpen,
    MultileanClose,
}

/**
 * A unit for linked list structure of tokens.
 * Each token represents a part of the document - a Waterproof Lean tag, document preamble, newline or text/code frangment.
 */
class Token {
    private readonly index: number;

    /**
     * Create a token and append it to `list`.
     */
    constructor(
        private readonly list: Token[],
        public readonly kind: Kind,
        public readonly range: BlockRange,
        public readonly line: number,
        public readonly groups: string[],
        public readonly namedGroups?: Record<string, string>,
    ) {
        this.index = list.length;
        list.push(this);
    }

    /**
     * Return the next token.
     */
    get next(): Token | undefined {
        return this.list.at(this.index + 1);
    }

    /**
     * Return the previous token.
     */
    get prev(): Token | undefined {
        if (this.index == 0) return undefined;
        return this.list.at(this.index - 1);
    }

    /**
     * Check if a token has one of given token kinds.
     */
    isOneOf(kinds: Kind[]): boolean {
        return kinds.includes(this.kind);
    }
}

const regexes: [RegExp, Kind][] = [
    [/^[\s\S]*#doc .*? =>\n/,             Kind.Preamble       ],
    [/(?<=\n)```lean\n/,                  Kind.CodeOpen       ],
    [/\n```(?=\n|$)/,                     Kind.CodeClose      ],
    [/(?<=\n):::input\n/,                 Kind.InputOpen      ],
    [/(?<=\n):::hint "(?<HintTitle>[\s\S]*?)"\n/,     Kind.HintOpen       ],
    [/\n:::(?=\n|$)/,                     Kind.Close          ],
    [/\$`[\s\S]*?`/,                      Kind.MathInline     ],
    [/\$\$`[\s\S]*?`/,                    Kind.MathDisplay    ],
    [/(?<=\n)::::multilean\n/,            Kind.MultileanOpen  ],
    [/\n::::(?=\n|$)/,                    Kind.MultileanClose ],
    // Match these last
    [/\n{1}/,                            Kind.Newline        ],
];
const flags: string = 'g';
const tokenRegex = new RegExp(regexes.map(([regex, toKind]) => {
    return '(?<' + Kind[toKind] + '>' + regex.source + ')'
}).join('|'), flags);


/**
 * Return token but fail if a token is undefined or not of one of given kinds.
 */
function expect(token: Token | undefined, kinds?: Kind[]): Token {
    if (token === undefined) {
        throw new Error('Expected a token but found nothing');
    } else if (kinds !== undefined && !token.isOneOf(kinds)) {
        throw new Error(`Expected one of [${kinds.join(', ')}] but found ${token?.kind}`);
    }

    return token;
}

/**
 * Parses the given token in the context of the given document, creating new blocks.
 *
 * @param doc - Document string.
 * @param token - Token that needs to be parsed.
 * @param blocks - List to append new blocks to.
 *
 * @return The next unparsed token or undefined on EOF.
 */
function handle(doc: string, token: Token, blocks: Block[]): Token | undefined {
    // Newline is significant if it's right before or after either code, input or hint block.
    const isSignificantNewline = (token: Token) =>
        token.kind === Kind.Newline
        && (token.prev?.isOneOf([Kind.Close, Kind.CodeClose, Kind.MultileanClose])
            || token.next?.isOneOf([Kind.CodeOpen, Kind.InputOpen, Kind.HintOpen, Kind.MultileanOpen]));

    if (token.kind === Kind.Preamble) {
        // Process the preamble.
      
        // We exclude the newline matched by the regex from the range to be able to 
        // have a newline block after the preamble, to prevent spawning spurious newlines.
        const range = {from: token.range.from, to: token.range.to - 1};
        // The visible part of the block excludes the last line, which has the form:
        // #doc ..... =>
        const innerRange = { from: token.range.from, to: doc.indexOf('#doc') - 1 };
        const content = doc.substring(innerRange.from, innerRange.to);

        const child = new CodeBlock(content, range, innerRange, token.line);
        blocks.push(new HintBlock(content, "🛠 Technical details", range, innerRange, token.line, [child]));
        const newlineRange = {from: token.range.to - 1, to: token.range.to}
        blocks.push(new NewlineBlock(newlineRange, newlineRange, token.line))

        return token.next;
    } else if (isSignificantNewline(token)) {
        // If newline is significant, add it as a newline block.
        const range = token.range;
        blocks.push(new NewlineBlock(range, range, token.line));

        return token.next;
    } else if (token.isOneOf([Kind.Text, Kind.Newline, Kind.MathInline])) {
        // Concatenate following inline math, text, and newlines.
        let head: Token = token;
        while (head.next
               && head.next.isOneOf([Kind.Text, Kind.Newline, Kind.MathInline])
               && !isSignificantNewline(head.next)) {
            head = head.next as Token;
        }

        const range = { from: token.range.from, to: head.range.to };
        const content = doc.substring(range.from, range.to);

        if (range.to - range.from > 1)
            blocks.push(new MarkdownBlock(content, range, range, token.line));

        return head.next;
    } else if (token.kind === Kind.CodeOpen) {
        // Process a code block.
        
        let head = token;
        // Iterate tokens until the code block closing token.
        // Only text (code) and newline are allowed inside a code block.
        while (head.kind !== Kind.CodeClose) {
            head = expect(head.next, [Kind.CodeClose, Kind.Text, Kind.Newline])
        }

        const range = { from: token.range.from, to: head.range.to };
        const innerRange = { from: token.range.to, to: head.range.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new CodeBlock(content, range, innerRange, token.line));

        return head.next;
    } else if (token.isOneOf([Kind.HintOpen, Kind.InputOpen])) {
        // Process a hint block or input block.
        
        const expected: Kind[] = [
            Kind.Close,
            Kind.Text,
            Kind.MathInline,
            Kind.MathDisplay,
            Kind.CodeOpen,
            Kind.Newline,
        ];

        let head: Token = expect(token.next, expected);
        const innerBlocks: Block[] = [];
        while (head && head.kind !== Kind.Close) {
            head = expect(handle(doc, head, innerBlocks));
        }

        const range = { from: token.range.from, to: head.range.to };
        const innerRange = { from: token.range.to, to: head.range.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        if (token.kind === Kind.HintOpen) {
            const title = token.namedGroups?.HintTitle ?? "";
            blocks.push(new HintBlock(content, title, range, innerRange, token.line, innerBlocks));
        } else {
            blocks.push(new InputAreaBlock(content, range, innerRange, token.line, innerBlocks));
        }

        return head.next;
    } else if (token.kind === Kind.MathDisplay) {
        const range = token.range;
        const innerRange = { from: range.from + 3, to: range.to - 1 };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new MathDisplayBlock(content, range, innerRange, token.line));

        return token.next;
    } else if (token.kind === Kind.MultileanOpen) {
        const expected: Kind[] = [
            Kind.MultileanClose,
            Kind.Text, Kind.MathInline, Kind.MathDisplay,
            Kind.CodeOpen, Kind.InputOpen, Kind.HintOpen, Kind.Newline,
        ];
        let head: Token = expect(token.next, expected);
        const innerBlocks: Block[] = [];
        while (head && head.kind !== Kind.MultileanClose) {
            head = expect(handle(doc, head, innerBlocks));
        }
        const range = { from: token.range.from, to: head.range.to };
        const innerRange = { from: token.range.to, to: head.range.from };
        const content = doc.substring(innerRange.from, innerRange.to);
        blocks.push(new ContainerBlock(content, "multilean", range, innerRange, token.line, innerBlocks));
        return head.next;
    } else {
        throw Error(`Unexpected token ${token.kind}`);
    }
}

/**
 * Split the `inputDocument` into a linked list of tokens
 * representing different tags or fragments in the document
 * and return the first one.
 *
 * @param inputDocument - Document to split in tokens.
 * 
 * @returns Linked list of tokens or unefined if no tokens obtained (document is empty).
 */
function tokenize(inputDocument: string): Token | undefined {
    // Match Waterproof Lean tag regexes in the document.
    const matches: RegExpMatchArray[] = Array.from(
        inputDocument.matchAll(tokenRegex)
    );

    const numOfNewlines = (range: BlockRange): number => {
        let count = 0;
        for (let i = range.from; i < range.to; i++)
            if (inputDocument.charAt(i) === "\n")
                count++;
        return count;
    };

    let newlines = 1;
    const tokens: Token[] = [];

    // Process each mached expression.
    for (const m of matches) {
        const pos = m.index as number;

        // Create 'Text' tokens for fragments inbetween regex matches
        const prev = tokens.at(-1);
        if (!prev && pos > 0) {
            const tok = new Token(tokens, Kind.Text, { from: 0, to: pos }, newlines, []);
            newlines += numOfNewlines(tok.range);
        } else if (prev && pos > prev.range.to + 1) {
            const tok = new Token(tokens, Kind.Text, { from: prev.range.to, to: pos }, newlines, []);
            newlines += numOfNewlines(tok.range);
        }

        // Check which regex matched and create a token of the appropriate kind
        for (const [_, toKind] of regexes) {
            if (m.groups && m.groups[Kind[toKind]]) {
                const range = { from: m.index as number, to: m.index as number + m[0].length };
                const tok = new Token(tokens, toKind, range, newlines, Array.from(m), m.groups as Record<string, string> | undefined);
                newlines += numOfNewlines(tok.range);
            }
        }
    }

    return tokens.at(0);
}

/**
 * Extract top-level blocks from a Lean-based document.
 */
export function topLevelBlocksLean(inputDocument: string): WaterproofDocument {
    // Split document into tokens.
    let head = tokenize(inputDocument);

    // Iteratively construct block structure of the document from the list of tokens.
    const blocks: Block[] = [];
    while (head) {
        head = handle(inputDocument, head, blocks);
    }

    return blocks.filter(b => b.range.from != b.range.to);
}
