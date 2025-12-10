import { Block, BlockRange, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, NewlineBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

type TokenKind =
    | 'Text'
    | 'Preamble'
    | 'CodeOpen'
    | 'CodeClose'
    | 'InputOpen'
    | 'HintOpen'
    | 'Close'
    | 'MultileanOpen'
    | 'OuterClose'
    | 'MathInline'
    | 'MathOpen'
    | 'MathClose'
    | 'Newline'
type Token = { kind: TokenKind, groups: string[], next?: Token, prev?: Token } & BlockRange;

const regexes: [RegExp, TokenKind][] = [
    [/^[\s\S]*#doc .*? =>\n/, 'Preamble'],
    [/(?<=\n)```lean\n/, 'CodeOpen'],
    [/\n```(?=\n|$)/, 'CodeClose'],
    [/(?<=\n):::input(?=\n)/, 'InputOpen'],
    [/(?<=\n):::hint "([\s\S]*?)"(?=\n)/, 'HintOpen'],
    [/(?<=\n):::(?=\n|$)/, 'Close'],
    [/::::multilean(?=\n)/, 'MultileanOpen'],
    [/\n::::(?=\n|$)/, 'OuterClose'],
    [/\$`[\s\S]*?`/, 'MathInline'],
    [/\$\$`/, 'MathOpen'],
    [/`/, 'MathClose'],
    [/\n{1}?/, 'Newline'],
];
const flags: string = 'g';
const tokenRegex = new RegExp(regexes.map(([regex, toKind]) => {
    return '(?<' + toKind + '>' + regex.source + ')'
}).join('|'), flags);


/**
 * Check if a token has one of given token kinds.
 */
function isOneOf(token: Token | undefined, kinds: TokenKind[]): boolean {
    if (!token) return false;
    return kinds.includes(token.kind);
}

/**
 * Return token but fail if a token is undefined or not of one of given kinds.
 */
function expect(token: Token | undefined, kinds?: TokenKind[]): Token {
    if (token === undefined) {
        throw new Error('Expected a token but found nothing');
    } else if (kinds !== undefined && !isOneOf(token, kinds)) {
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
        token.kind === 'Newline'
        && (isOneOf(token.prev, ['Close', 'OuterClose'])
            || isOneOf(token.next, ['CodeOpen', 'InputOpen', 'HintOpen', 'MultileanOpen']));

    if (token.kind === 'Preamble') {
        const range = { from: token.from, to: token.to };
        const content = doc.substring(token.from, token.to);

        const child = new CodeBlock(content, range, range);
        blocks.push(new HintBlock(content, "Preamble", range, range, [child]));

        return token.next;
    } else if (isSignificantNewline(token)) {
        const range = { from: token.from, to: token.to };
        blocks.push(new NewlineBlock(range, range));

        return token.next;
    } else if (token.kind === 'Text' || token.kind === 'Newline') {
        // concatenate following inline math, text, and newlines
        let head: Token = token;
        while (head.next
               && isOneOf(head.next, ['Text', 'Newline', 'MathInline'])
               && !isSignificantNewline(head.next)) {
            head = head.next as Token;
        }

        const range = { from: token.from, to: head.to };
        const content = doc.substring(range.from, range.to);

        if (range.to - range.from > 1)
            blocks.push(new MarkdownBlock(content, range, range));

        return head.next;
    } else if (token.kind === 'CodeOpen') {
        let head = token;
        while (head.kind !== 'CodeClose') {
            head = expect(head.next, ['CodeClose', 'Text', 'Newline'])
        }

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new CodeBlock(content, range, innerRange));

        return head.next;
    } else if (token.kind === 'HintOpen' || token.kind === 'InputOpen') {
        const expected: TokenKind[] = ['Close', 'Text', 'MathInline',
                                       'MathOpen', 'CodeOpen', 'Newline'];
        let head: Token = expect(token.next, expected);
        const innerBlocks: Block[] = [];
        while (head && head.kind !== 'Close') {
            head = expect(handle(doc, head, innerBlocks));
        }

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        if (token.kind === 'HintOpen') {
            const title = token.groups[1];
            blocks.push(new HintBlock(content, title, range, innerRange, innerBlocks));
        } else {
            blocks.push(new InputAreaBlock(content, range, innerRange, innerBlocks));
        }

        return head.next;
    } else if (token.kind === 'MultileanOpen') {
        // parse everything to the corresponding close
        let head = expect(token.next);
        while (head.kind !== 'OuterClose') {
            head = expect(handle(doc, head, blocks));
        }
        return head.next;
    } else if (token.kind === 'MathOpen') {
        let head = token;
        do {
            head = expect(head.next, ['Text', 'Newline', 'MathClose']);
        } while (head.kind != 'MathClose');

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new MathDisplayBlock(content, range, innerRange));

        return head.next;
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

    let head: Token | undefined = undefined
    let tail: Token | undefined = undefined;
    for (const m of matches) {
        const pos = m.index as number;
        // Create 'Text' tokens for fragments inbetween regex matches
        if (!tail && pos > 0) {
            tail = { kind: 'Text', from: 0, to: pos, groups: [] };
            head = tail;
        } else if (tail && pos > tail.to + 1) {
            tail.next = { kind: 'Text', from: tail.to, to: pos, groups: [], prev: tail };
            tail = tail.next;
        }

        for (const [_, toKind] of regexes) {
            if (m.groups && m.groups[toKind]) {
                const token = {
                    kind: toKind,
                    from: m.index as number, to: m.index as number + m[0].length,
                    groups: Array.from(m),
                    prev: tail,
                };
                if (tail) tail.next = token;
                else {
                    head = token;
                }
                tail = token;
            }
        }
    }

    return head;
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
