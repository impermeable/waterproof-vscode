const Position = class {
    constructor(public line: number, public character: number) {}
    translate(lineDelta: number, charDelta: number) {
        return new Position(this.line + lineDelta, this.character + charDelta);
    }
    isAfter(other: InstanceType<typeof Position>) {
        return this.line > other.line
            || (this.line === other.line && this.character > other.character);
    }
    isBeforeOrEqual(other: InstanceType<typeof Position>) {
        return !this.isAfter(other);
    }
};

const Range = class {
    constructor(
        public start: InstanceType<typeof Position>,
        public end:   InstanceType<typeof Position>,
    ) {}
    intersection(other: InstanceType<typeof Range>): InstanceType<typeof Range> | undefined {
        const startLine = Math.max(this.start.line, other.start.line);
        const endLine   = Math.min(this.end.line,   other.end.line);
        if (startLine > endLine) return undefined;
        return new Range(new Position(startLine, 0), new Position(endLine, 0));
    }
    get isEmpty() {
        return this.start.line === this.end.line && this.start.character === this.end.character;
    }
};

export function createVscodeLspMock() {
    return {
        Position,
        Range,
        DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2, Hint: 3 },
        EventEmitter: class {
            fire()  {}
            event = () => ({ dispose: () => {} });
        },
        workspace: {
            getConfiguration:         jest.fn(() => ({ get: jest.fn((_key: string, def?: unknown) => def) })),
            onDidChangeConfiguration: jest.fn(() => ({ dispose: jest.fn() })),
            onDidChangeTextDocument:  jest.fn(() => ({ dispose: jest.fn() })),
        },
        languages: {
            createDiagnosticCollection: jest.fn(() => ({ set: jest.fn(), dispose: jest.fn() })),
            getDiagnostics:             jest.fn(() => []),
            onDidChangeDiagnostics:     jest.fn(() => ({ dispose: jest.fn() })),
        },
        window: {
            createOutputChannel: jest.fn(() => ({
                appendLine: jest.fn(),
                dispose:    jest.fn(),
            })),
        },
    };
}
