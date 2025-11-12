import { Block, CodeBlock, HintBlock, InputAreaBlock, MarkdownBlock, MathDisplayBlock, WaterproofDocument } from "@impermeable/waterproof-editor";

type TokenBase = { pos: number, length: number };

type EOF = { kind: 'EOF' } & TokenBase;
type Text = { kind: 'Text', content: string } & TokenBase;
type CodeOpen = { kind: 'CodeOpen' } & TokenBase;
type CodeClose = { kind: 'CodeClose' } & TokenBase;
type InputOpen = { kind: 'InputOpen' } & TokenBase;
type HintOpen = { kind: 'HintOpen', title: string } & TokenBase;
type MultileanOpen = { kind: 'MultileanOpen' } & TokenBase;
type Close = { kind: 'Close' } & TokenBase;
type MathInline = { kind: 'MathInline', content: string } & TokenBase;
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

const tagRegex = /(?:\r?\n|^)(?:```lean|```|:::input|:::hint "([\s\S]*?)"|:::multilean|:::)(?:\r?\n|$)|\$`[\s\S]*?`|\$\$`|`/gm;

function handle(token: Token, blocks: Block[], tail: Token[]) {
    if (token.kind === 'Text') {
        let content = token.content;

        while (peek(tail)?.kind === 'MathInline' || peek(tail)?.kind === 'Text') {
            const math = accept(['MathInline', 'Text'], tail) as MathInline;
            content += math.content;
        }

        const range = { from: token.pos, to: token.pos + content.length };

        if (range.to - range.from > 1)
            blocks.push(new MarkdownBlock(token.content, range, range));
    } else if (token.kind === 'CodeOpen') {
        let head = accept(['CodeClose', 'Text'], tail);

        if (head.kind === 'Text') {
            const close = accept('CodeClose', tail);
            const body = head as Text;

            let stop = close.pos + close.length;

            const range = { from: token.pos, to: stop };
            const innerRange = { from: body.pos, to: close.pos };

            blocks.push(new CodeBlock(body.content, range, innerRange));
        }
    } else if (token.kind === 'HintOpen') {
        const expected = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
        let head = accept(expected, tail);
        const innerBlocks: Block[] = [];
        while (head.kind !== 'Close') {
            handle(head, innerBlocks, tail);
            head = accept(expected, tail);
        }

        const range = { from: token.pos, to: head.pos + head.length };
        const innerRange = { from: token.pos + token.length, to: head.pos };
        const content = innerBlocks.map(c => c.stringContent).join('');

        blocks.push(new HintBlock(content, token.title, range, innerRange, innerBlocks));
    } else if (token.kind === 'InputOpen') {
        const expected = ['Close', 'Text', 'MathInline', 'MathOpen', 'CodeOpen'];
        let head = accept(expected, tail);
        const innerBlocks: Block[] = [];
        while (head.kind !== 'Close') {
            handle(head, innerBlocks, tail);
            head = accept(expected, tail);
        }

        const range = { from: token.pos, to: head.pos + head.length };
        const innerRange = { from: token.pos + token.length, to: head.pos };
        const content = innerBlocks.map(c => c.stringContent).join('');

        blocks.push(new InputAreaBlock(content, range, innerRange, innerBlocks));
    } else if (token.kind === 'MultileanOpen') {
        // parse everything to the corresponding close
        let head = accept(undefined, tail);
        while (head.kind !== 'Close') {
            handle(head, blocks, tail);
            head = accept(undefined, tail);
        }
    } else if (token.kind === 'MathOpen') {
        const body = accept('Text', tail) as Text;
        const close = accept('MathClose', tail);
        const range = { from: token.pos, to: close.pos + close.length };
        const innerRange = { from: body.pos, to: body.pos + body.length };

        blocks.push(new MathDisplayBlock(body.content, range, innerRange));
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
            return { kind: 'CodeOpen', pos: pos, length: m[0].length };
        } else if (m[0].match(/^```$/m)) {
            return { kind: 'CodeClose', pos: pos, length: m[0].length };
        } else if (m[0].match(/^:::input$/m)) {
            return { kind: 'InputOpen', pos: pos, length: m[0].length };
        } else if (m[0].match(/^:::hint /m)) {
            return { kind: 'HintOpen', title: m[1], pos: pos, length: m[0].length };
        } else if (m[0].match(/^:::multilean$/m)) {
            return { kind: 'MultileanOpen', pos: pos, length: m[0].length };
        } else if (m[0].match(/^:::$/m)) {
            return { kind: 'Close', pos: pos, length: m[0].length };
        } else if (m[0] === '$$`') {
            return { kind: 'MathOpen', pos: pos, length: m[0].length };
        } else if (m[0].match('$`.*`')) {
            return { kind: 'MathInline', content: m[0], pos: pos, length: m[0].length };
        } else if (m[0] === '`') {
            return { kind: 'MathClose', pos: pos, length: m[0].length };
        } else {
            return null;
        }
    }).filter(v => v !== null)
    // insert intermediate text tokens with the actual content
    .concat([{ kind: 'EOF', pos: inputDocument.length, length: 0 }])
    .reduce((acc: Token[], tok: Token, _i, _arr): Token[] => {
        const prev = acc.at(-1);
        if (!prev) {
            const content = inputDocument.substring(0, tok.pos);
            acc.push({ kind: 'Text', content: content, pos: tok.pos, length: content.length });
            acc.push(tok);
            return acc;
        }

        const content = inputDocument.substring(prev.pos + prev.length, tok.pos);

        if (prev.kind !== 'Text') {
            acc.push({ kind: 'Text', content: content, pos: tok.pos, length: content.length });
        }
        acc.push(tok);
        return acc;
    }, []);

    const blocks: Block[] = [];
    while (tokens.length) {
        const token = tokens.shift() as Token;
        handle(token, blocks, tokens);
    }

    return blocks.filter(b => b.range.from != b.range.to);
}
