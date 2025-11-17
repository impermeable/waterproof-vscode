import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

type TokenBase = { from: number, to: number };

type EOF = { kind: 'EOF' } & TokenBase;
type Text = { kind: 'Text' } & TokenBase;
type CodeOpen = { kind: 'CodeOpen' } & TokenBase;
type CodeClose = { kind: 'CodeClose' } & TokenBase;
type InputOpen = { kind: 'InputOpen' } & TokenBase;
type HintOpen = { kind: 'HintOpen', title: string } & TokenBase;
type MultileanOpen = { kind: 'MultileanOpen' } & TokenBase;
type Close = { kind: 'Close' } & TokenBase;
type MathInline = { kind: 'MathInline' } & TokenBase;
type MathOpen = { kind: 'MathOpen' } & TokenBase;
type MathClose = { kind: 'MathClose' } & TokenBase;

type Token =
    | EOF
    | Text
    | CodeOpen
    | CodeClose
    | InputOpen
    | HintOpen
    | MultileanOpen
    | Close
    | MathInline
    | MathOpen
    | MathClose

const tagRegex = /```lean\n|\n```(?!\S)|:::input\n|:::hint "([\s\S]*?)"\n|:::multilean\n|\n:::(?!\S)|\$`[\s\S]*?`|\$\$`|`/g;

function handle(doc: string, token: Token, blocks: Block[], tail: Token[]) {
    if (token.kind === 'Text') {
        let content = doc.substring(token.from, token.to);

        while (peek(tail)?.kind === 'MathInline' || peek(tail)?.kind === 'Text') {
            const math = accept(['MathInline', 'Text'], tail) as MathInline;
            content += doc.substring(math.from, math.to);
        }

        const range = { from: token.from, to: token.to };

        if (range.to - range.from > 1)
            blocks.push(new MarkdownBlock(content, range, range));
    } else if (token.kind === 'CodeOpen') {
        let head = accept(['CodeClose', 'Text'], tail);

        if (head.kind === 'Text') {
            const close = accept('CodeClose', tail);
            const body = head as Text;

            const range = { from: token.from, to: close.to };
            const innerRange = { from: body.from, to: body.to };
            const content = doc.substring(body.from, body.to);

            blocks.push(new CodeBlock(content, range, innerRange));
        }
    } else if (token.kind === 'HintOpen') {
        const expected = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
        let head = accept(expected, tail);
        const innerBlocks: Block[] = [];
        while (head.kind !== 'Close') {
            handle(doc, head, innerBlocks, tail);
            head = accept(expected, tail);
        }

        const range = { from: token.from, to: head.to };
        const innerRange = { from: token.to, to: head.from };
        const content = doc.substring(innerRange.from, innerRange.to);

        blocks.push(new HintBlock(content, token.title, range, innerRange, innerBlocks));
    } else if (token.kind === 'InputOpen') {
        const expected = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
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
        while (head.kind !== 'Close') {
            handle(doc, head, blocks, tail);
            head = accept(undefined, tail);
        }
    } else if (token.kind === 'MathOpen') {
        const body = accept('Text', tail) as Text;
        const close = accept('MathClose', tail);
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

function accept(kind: string | string[] | undefined, tail: Token[]): Token {
    const head = tail.shift();

    let kinds;
    if (typeof kind === 'string')
        kinds = [kind];
    else
        kinds = kind;

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
        inputDocument.matchAll(tagRegex)
    );

    const tokens: Token[] = matches.map((m: RegExpMatchArray): Token | null => {
        const pos = m.index as number;

        if (m[0].match(/^```lean$/m)) {
            return { kind: 'CodeOpen', from: pos, to: pos + m[0].length };
        } else if (m[0].match(/^```$/m)) {
            return { kind: 'CodeClose', from: pos, to: pos + m[0].length };
        } else if (m[0].match(/^:::input$/m)) {
            return { kind: 'InputOpen', from: pos, to: pos + m[0].length };
        } else if (m[0].match(/^:::hint /m)) {
            return { kind: 'HintOpen', title: m[1], from: pos, to: pos + m[0].length };
        } else if (m[0].match(/^:::multilean$/m)) {
            return { kind: 'MultileanOpen', from: pos, to: pos + m[0].length };
        } else if (m[0].match(/^:::$/m)) {
            return { kind: 'Close', from: pos, to: pos + m[0].length };
        } else if (m[0] === '$$`') {
            return { kind: 'MathOpen', from: pos, to: pos + m[0].length };
        } else if (m[0].match('$`.*`')) {
            return { kind: 'MathInline', from: pos, to: pos + m[0].length };
        } else if (m[0] === '`') {
            return { kind: 'MathClose', from: pos, to: pos + m[0].length };
        } else {
            return null;
        }
    }).filter(v => v !== null)
    // insert intermediate text tokens with the actual content
    .concat([{ kind: 'EOF', from: inputDocument.length, to: inputDocument.length }])
    .reduce((acc: Token[], tok: Token, _i, _arr): Token[] => {
        const prev = acc.at(-1);
        if (!prev) {
            acc.push({ kind: 'Text', from: 0, to: tok.from });
            acc.push(tok);
            return acc;
        }

        if (prev.kind !== 'Text') {
            acc.push({ kind: 'Text', from: prev.to, to: tok.from });
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
