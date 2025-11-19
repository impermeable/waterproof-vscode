import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

type TokenType =
    | 'EOF'
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
type Token = { kind: TokenType, from: number, to: number, groups: string[] };

const regexes: [RegExp, TokenType][] = [
    [/^[\s\S]*#doc .*? =>\n/, 'Preamble'],
    [/```lean\n/, 'CodeOpen'],
    [/\n```(?!\S)/, 'CodeClose'],
    [/:::input\n/, 'InputOpen'],
    [/:::hint "([\s\S]*?)"\n/, 'HintOpen'],
    [/\n:::(?!\S)/, 'Close'],
    [/::::multilean\n/, 'MultileanOpen'],
    [/\n::::(?!\S)/, 'OuterClose'],
    [/\$`[\s\S]*?`/, 'MathInline'],
    [/\$\$`/, 'MathOpen'],
    [/`/, 'MathClose'],
];
const flags: string = 'g';
const tokenRegex = new RegExp(regexes.map(([regex, tokType]) => {
    return '(?<' + tokType + '>' + regex.source + ')'
}).join('|'), flags);

function handle(doc: string, token: Token, blocks: Block[], tail: Token[]) {
    if (token.kind === 'Preamble') {
        const range = { from: token.from, to: token.to };
        const content = doc.substring(token.from, token.to);

        const child = new CodeBlock(content, range, range);
        blocks.push(new HintBlock(content, "Preamble", range, range, [child]));
    } else if (token.kind === 'Text') {
        const start = token.from;
        let stop = token.to;

        // concatenate following inline math and text
        while (peek(tail)?.kind === 'MathInline' || peek(tail)?.kind === 'Text') {
            const chunk = accept(['MathInline', 'Text'], tail);
            stop = chunk.to;
        }

        let content = doc.substring(start, stop);
        const range = { from: start, to: stop };

        if (range.to - range.from > 1)
            blocks.push(new MarkdownBlock(content, range, range));
    } else if (token.kind === 'CodeOpen') {
        let head = accept(['CodeClose', 'Text'], tail);

        if (head.kind === 'Text') {
            const close = accept(['CodeClose'], tail);

            const range = { from: token.from, to: close.to };
            const innerRange = { from: head.from, to: head.to };
            const content = doc.substring(head.from, head.to);

            blocks.push(new CodeBlock(content, range, innerRange));
        }
    } else if (token.kind === 'HintOpen') {
        const expected: TokenType[] = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
        let head = accept(expected, tail);
        const innerBlocks: Block[] = [];
        while (head.kind !== 'Close') {
            handle(doc, head, innerBlocks, tail);
            head = accept(expected, tail);
        }

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);
        const title = token.groups[1];

        blocks.push(new HintBlock(content, title, range, innerRange, innerBlocks));
    } else if (token.kind === 'InputOpen') {
        const expected: TokenType[] = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
        let head = accept(expected, tail);
        const innerBlocks: Block[] = [];
        while (head.kind !== 'Close') {
            handle(doc, head, innerBlocks, tail);
            head = accept(expected, tail);
        }

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new InputAreaBlock(content, range, innerRange, innerBlocks));
    } else if (token.kind === 'MultileanOpen') {
        // parse everything to the corresponding close
        let head = accept(undefined, tail);
        while (head.kind !== 'OuterClose') {
            handle(doc, head, blocks, tail);
            head = accept(undefined, tail);
        }
    } else if (token.kind === 'MathOpen') {
        const body = accept(['Text'], tail);
        const close = accept(['MathClose'], tail);
        const range = { from: token.from, to: close.to };
        const innerRange = { from: token.to, to: close.from };
        const content = doc.substring(body.from, body.to);

        blocks.push(new MathDisplayBlock(content, range, innerRange));
    } else if (token.kind === 'EOF') {
        return;
    } else {
        throw Error(`Unexpected token ${token.kind}`);
    }
}

function accept(kinds: TokenType[] | undefined, tail: Token[]): Token {
    const head = tail.shift();

    if (head === undefined) {
        throw new Error('Expected a token but found nothing');
    } else if (!kinds?.includes(head.kind) && kinds !== undefined) {
        throw new Error(`Expected one of [${kinds.join(', ')}] but found ${head?.kind}`);
    }
    else return head;
}

function peek(tail: Token[]): Token | undefined {
    return tail.at(0);
}

export function topLevelBlocksLean(inputDocument: string): WaterproofDocument {
    const matches: RegExpMatchArray[] = Array.from(
        inputDocument.matchAll(tokenRegex)
    );

    const tokens: Token[] = matches.map((m: RegExpMatchArray): Token | null => {
        for (const [regex, tokType] of regexes) {
            if (m[0].match(new RegExp('^' + regex.source + '$'))) {
                return {
                    kind: tokType,
                    from: m.index as number, to: m.index as number + m[0].length,
                    groups: Array.from(m),
                };
            }
        }

        return null;
    }).filter(v => v !== null)
    .concat([{ kind: 'EOF', from: inputDocument.length, to: inputDocument.length, groups: [] }])
    // insert intermediate text tokens with the actual content
    .reduce((acc: Token[], tok: Token, _i, _arr): Token[] => {
        const prev = acc.at(-1);
        if (!prev) {
            acc.push({ kind: 'Text', from: 0, to: tok.from, groups: [] });
            acc.push(tok);
            return acc;
        }

        if (prev.kind !== 'Text') {
            acc.push({ kind: 'Text', from: prev.to, to: tok.from, groups: [] });
        }
        acc.push(tok);
        return acc;
    }, []);

    const blocks: Block[] = [];
    while (tokens.length) {
        const token = tokens.shift() as Token;
        handle(inputDocument, token, blocks, tokens);
    }

    return blocks.filter(b => b.range.from != b.range.to);
}
