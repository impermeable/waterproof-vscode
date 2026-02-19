import { Block, BlockRange, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, NewlineBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

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
    [/(?<=\n):::hint "([\s\S]*?)"(?=\n)/, Kind.HintOpen       ],
    [/\n:::(?=\n|$)/,                     Kind.Close          ],
    [/\$`[\s\S]*?`/,                      Kind.MathInline     ],
    [/\$\$`[\s\S]*?`/,                    Kind.MathDisplay    ],
    [/(?<=\n)::::multilean\n/,            Kind.MultileanOpen  ],
    [/\n::::(?=\n|$)/,                    Kind.MultileanClose ],
    // Match these last
    [/\n{1}?/,                            Kind.Newline        ],
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
 * Parse the given token in the context of the given document, creating new blocks.
 *
 * @param doc document string
 * @param token token that needs to be parsed
 * @param blocks list to append new blocks to
 *
 * @return the next unparsed token or undefined on EOF
 */
function handle(doc: string, token: Token, blocks: Block[]): Token | undefined {
    const isSignificantNewline = (token: Token) =>
        token.kind === Kind.Newline
        && (token.prev?.isOneOf([Kind.Close])
            || token.next?.isOneOf([Kind.CodeOpen, Kind.InputOpen, Kind.HintOpen]));

    if (token.kind === Kind.Preamble) {
        const range = token.range;
        const content = doc.substring(range.from, range.to);

        const child = new CodeBlock(content, range, range, token.line);
        blocks.push(new HintBlock(content, "🛠 Technical details", range, range, token.line, [child]));

        return token.next;
    } else if (isSignificantNewline(token)) {
        const range = token.range;
        blocks.push(new NewlineBlock(range, range, token.line));

        return token.next;
    } else if (token.isOneOf([Kind.Text, Kind.Newline, Kind.MathInline])) {
        // concatenate following inline math, text, and newlines
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
        let head = token;
        while (head.kind !== Kind.CodeClose) {
            head = expect(head.next, [Kind.CodeClose, Kind.Text, Kind.Newline])
        }

        const range = { from: token.range.from, to: head.range.to };
        const innerRange = { from: token.range.to, to: head.range.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new CodeBlock(content, range, innerRange, token.line));

        return head.next;
    } else if (token.isOneOf([Kind.HintOpen, Kind.InputOpen])) {
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
            const title = token.groups[1];
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
    } else if (token.isOneOf([Kind.MultileanOpen, Kind.MultileanClose])) {
        // We skip to the next token as we don't want the multilean tags to be shown in the editor.
        return token.next;
    } else {
        throw Error(`Unexpected token ${token.kind}`);
    }
}

/**
 * Split the input document into a linked list of tokens
 * representing different tags or fragments in the document
 * and return the first one.
 */
function tokenize(inputDocument: string): Token | undefined {
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
                const tok = new Token(tokens, toKind, range, newlines, Array.from(m));
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
    let head = tokenize(inputDocument);

    const blocks: Block[] = [];
    while (head) {
        head = handle(inputDocument, head, blocks);
    }

    return blocks.filter(b => b.range.from != b.range.to);
}
