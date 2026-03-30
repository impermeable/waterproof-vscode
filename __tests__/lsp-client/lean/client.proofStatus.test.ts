jest.mock("vscode", () => {
    const Position = class {
        constructor(public line: number, public character: number) {}
        translate(lineDelta: number, charDelta: number) {
            return new Position(this.line + lineDelta, this.character + charDelta);
        }
        isAfter(other: InstanceType<typeof Position>) {
            return this.line > other.line
                || (this.line === other.line && this.character > other.character);
        }
    };

    const Range = class {
        constructor(
            public start: InstanceType<typeof Position>,
            public end:   InstanceType<typeof Position>
        ) {}
        intersection(other: InstanceType<typeof Range>): InstanceType<typeof Range> | undefined {
            const startLine = Math.max(this.start.line, other.start.line);
            const endLine   = Math.min(this.end.line,   other.end.line);
            if (startLine > endLine) return undefined;
            return new Range(new Position(startLine, 0), new Position(endLine, 0));
        }
        get isEmpty() {
            return this.start.line === this.end.line
                && this.start.character === this.end.character;
        }
    };

    return {
        Position,
        Range,
        DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2, Hint: 3 },
        EventEmitter: class {
            fire()  {}
            event = () => ({ dispose: () => {} });
        },
        workspace: {
            getConfiguration:         jest.fn(() => ({ get: jest.fn((_key: string, def?: any) => def) })),
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
}, { virtual: true });

jest.mock("vscode-languageclient", () => ({
    LogTraceNotification:  { type: "$/logTrace" },
    RequestType:           jest.fn().mockImplementation(() => ({})),
    NotificationType:      jest.fn().mockImplementation(() => ({})),
    DocumentSymbolRequest: { type: {} },
}), { virtual: true });

jest.mock("vscode-languageserver-types", () => ({
    VersionedTextDocumentIdentifier: { create: jest.fn((uri, v) => ({ uri, version: v })) },
}), { virtual: true });

jest.mock("../../../shared",        () => ({ MessageType: {}, FileProgressKind: { Processing: 1 } }), { virtual: true });
jest.mock("../../../lib/types",     () => ({}), { virtual: true });
jest.mock("../../../src/helpers",   () => ({
    WaterproofConfigHelper: { get: jest.fn(() => false) },
    WaterproofLogger:       { log: jest.fn(), debug: jest.fn() },
    WaterproofSetting:      {},
    qualifiedSettingName:   jest.fn(s => s),
}));
jest.mock("../sentenceManager",     () => ({ SentenceManager: class { onProgress() {} dispose() {} } }), { virtual: true });
jest.mock("../clientTypes",         () => ({}), { virtual: true });
jest.mock("../requestTypes",        () => ({ convertToSimple: jest.fn() }), { virtual: true });
jest.mock("../qedStatus",           () => ({
    findOccurrences: jest.fn((substr: string, str: string) => {
        const indices: number[] = [];
        const substrLen = substr.length;
        for (let i = 0; (i = str.indexOf(substr, i)) >= 0; i += substrLen) {
            indices.push(i);
        }
        return indices;
    }),
}), { virtual: true });
jest.mock("./requestTypes",         () => ({
    leanFileProgressNotificationType: "$/lean/fileProgress",
    leanGoalRequestType:              "$/lean/plainGoal",
}), { virtual: true });
jest.mock("@impermeable/waterproof-editor", () => ({
    InputAreaStatus: { Correct: "Correct", Incorrect: "Incorrect", Invalid: "Invalid" },
}), { virtual: true });
jest.mock("@leanprover/infoview-api", () => ({}), { virtual: true });

import { Range, Position, DiagnosticSeverity } from "vscode";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { LeanLspClient } from "../../../src/lsp-client/lean/client";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
const INPUT_AREA = new Range(new Position(0, 0), new Position(5, 0));

const FAKE_DOCUMENT = {
    uri:        { toString: () => "file:///test.lean", path: "/test.lean" },
    version:    1,
    getText:    () => ":::input\n\n:::\n",
    offsetAt:   (pos: any) => pos.line * 100 + pos.character,
    positionAt: (offset: number) => new Position(Math.floor(offset / 100), offset % 100),
    lineCount:  10,
} as any;

function makeClientDouble() {
    return {
        isRunning:              jest.fn(() => true),
        start:                  jest.fn(() => Promise.resolve()),
        dispose:                jest.fn(() => Promise.resolve()),
        onNotification:         jest.fn(() => ({ dispose: jest.fn() })),
        sendRequest:            jest.fn(),
        middleware:             { handleDiagnostics: undefined as any },
        protocol2CodeConverter: { asRange: (r: any) => r },
        code2ProtocolConverter: { asUri: (u: any) => u.toString(), asDiagnostic: (d: any) => d },
    };
}

function makeClient(isBusy = false) {
    const clientDouble = makeClientDouble();
    const instance = new LeanLspClient(
        jest.fn(() => clientDouble) as any,
        { appendLine: jest.fn() } as any,
    );
    (instance as any).activeDocument = FAKE_DOCUMENT;
    (instance as any).webviewManager = {
        postMessage: jest.fn(),
        postAndCacheMessage: jest.fn(),
        has: jest.fn(() => true),
    };
    (instance as any).isBusy = isBusy;
    return instance;
}

const call = (instance: LeanLspClient, diags: any[] = [], area = INPUT_AREA) =>
    (instance as any).determineProofStatus(FAKE_DOCUMENT, area, diags);

const diag = (startLine: number, endLine: number, severity: number) => ({
    message:  "test",
    severity,
    range: new Range(new Position(startLine, 0), new Position(endLine, 0)),
});

const messageDiag = (message: string, startLine: number, startCharacter = 0) => ({
    message,
    range: new Range(
        new Position(startLine, startCharacter),
        new Position(startLine, startCharacter),
    ),
});

const makeDocument = (content: string) => ({
    ...FAKE_DOCUMENT,
    getText:    () => content,
    positionAt: (offset: number) => new Position(0, offset),
    offsetAt:   (pos: any) => pos.character,
}) as any;

// ===========================================================================
// Tests
// ===========================================================================
describe("LeanLspClient.determineProofStatus", () => {

    it("returns Incorrect when isBusy", async () => {
        const instance = makeClient(true);
        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect for an Error diagnostic inside the area", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance, [diag(1, 3, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect for an Error diagnostic on the area boundary", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance, [diag(4, 5, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Incorrect);
    });

    it("ignores an Error diagnostic outside the area", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance, [diag(10, 11, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Correct);
    });

    it("does not treat Warning/Info/Hint diagnostics as blocking", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance, [
            diag(1, 2, DiagnosticSeverity.Warning),
            diag(2, 3, DiagnosticSeverity.Information),
            diag(3, 4, DiagnosticSeverity.Hint),
        ])).toBe(InputAreaStatus.Correct);
    });

    it("returns Incorrect when goals are non-empty", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [{ type: "⊢ False" }] });
        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Correct when idle, no errors, and goals are empty", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance)).toBe(InputAreaStatus.Correct);
    });

    it("returns Incorrect when requestGoals resolves with null", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue(null);
        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect when requestGoals resolves with undefined", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue(undefined);
        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

});

describe("LeanLspClient.earlyProofStatus", () => {
    const lowerBound = new Position(2, 0);
    const inputArea = new Range(new Position(2, 0), new Position(6, 0));

    const earlyProofStatus = (diags: any[]) => {
        const instance = makeClient();
        // @ts-expect-error protected
        return instance.earlyProofStatus(diags, lowerBound, inputArea);
    };

    it("returns Invalid for a sorry diagnostic inside bounds", () => {
        expect(earlyProofStatus([
            messageDiag("declaration uses 'sorry'", 4),
        ])).toBe(InputAreaStatus.Invalid);
    });

    it("returns Incorrect for a Try these hint inside bounds", () => {
        expect(earlyProofStatus([
            messageDiag("Try these:\n  exact h", 4),
        ])).toBe(InputAreaStatus.Incorrect);
    });

    it("returns null when matching diagnostic is at lowerBound", () => {
        expect(earlyProofStatus([
            messageDiag("declaration uses 'sorry'", 2, 0),
        ])).toBeNull();
    });

    it("returns null when matching diagnostic is after input area end", () => {
        expect(earlyProofStatus([
            messageDiag("Try these:\n  simp", 7),
        ])).toBeNull();
    });

    it("returns null for non-matching messages", () => {
        expect(earlyProofStatus([
            messageDiag("type mismatch", 4),
        ])).toBeNull();
    });

    it("returns Invalid when only sorry matches among mixed diagnostics", () => {
        expect(earlyProofStatus([
            messageDiag("type mismatch", 4),
            messageDiag("declaration uses 'sorry'", 5),
        ])).toBe(InputAreaStatus.Invalid);
    });

    it("prioritizes Hint over sorry when both messages are present", () => {
        expect(earlyProofStatus([
            messageDiag("declaration uses 'sorry'", 4),
            messageDiag("Try these:\n  exact h", 5),
        ])).toBe(InputAreaStatus.Incorrect);
    });

    it("prioritizes Hint over sorry even within the same diagnostic message", () => {
        expect(earlyProofStatus([
            messageDiag("Try these:\n  exact h\n\ndeclaration uses 'sorry'", 4),
        ])).toBe(InputAreaStatus.Incorrect);
    });
});

describe("LeanLspClient.getInputAreas ordering", () => {
    it("returns input areas in source order", () => {
        const instance = makeClient();
        const content = [
            "before",
            ":::input",
            "first",
            ":::",
            "between",
            ":::input",
            "second",
            ":::",
            "",
        ].join("\n");
        const document = makeDocument(content);

        // @ts-expect-error protected
        const areas = instance.getInputAreas(document) as Range[];
        expect(areas).toHaveLength(2);

        const starts = areas.map(area => document.offsetAt(area.start));
        const firstOpen = content.indexOf(":::input\n");
        const secondOpen = content.indexOf(":::input\n", firstOpen + 1);

        expect(starts).toEqual([firstOpen, secondOpen]);
        expect(starts).toEqual([...starts].sort((a, b) => a - b));
    });

    it("keeps consecutive areas monotonic for lower-bound logic", () => {
        const instance = makeClient();
        const content = [
            ":::input",
            "a",
            ":::",
            ":::input",
            "b",
            ":::",
            ":::input",
            "c",
            ":::",
            "",
        ].join("\n");
        const document = makeDocument(content);

        // @ts-expect-error protected
        const areas = instance.getInputAreas(document) as Range[];
        expect(areas).toHaveLength(3);

        const starts = areas.map(area => document.offsetAt(area.start));
        const ends = areas.map(area => document.offsetAt(area.end));

        for (let i = 1; i < areas.length; i++) {
            expect(starts[i]).toBeGreaterThan(starts[i - 1]);
            expect(ends[i - 1]).toBeLessThanOrEqual(starts[i]);
        }
    });

    it("stays sorted on production-like multilean content", () => {
        const instance = makeClient();
        const content = [
            "#doc (WaterproofGenre) \"Index\" =>",
            "",
            "::::multilean",
            "",
            "## ATC - 003",
            "```lean",
            "Example \"ATC - 003\"",
            "  Given:",
            "  Assume:",
            "  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a",
            "Proof:",
            "```",
            ":::input",
            "```lean",
            "",
            "```",
            ":::",
            "",
            "## ATC - 009",
            ":::hint \"Show hint\"",
            "  hello",
            ":::",
            "```lean",
            "Example \"ATC - 009\"",
            "  Given:",
            "  Assume:",
            "  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a",
            "Proof:",
            "```",
            ":::input",
            "```lean",
            "",
            "```",
            ":::",
            "",
            "## ATC - 014",
            "```lean",
            "Example \"ATC - 014\"",
            "  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)",
            "  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)",
            "  Conclusion: (f ∘ u) converges to f x₀",
            "Proof:",
            "```",
            ":::input",
            "```lean",
            "  Fix ε > 0",
            "  By hf applied to ε using that ε > 0 we get δ such that",
            "    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)",
            "```",
            ":::",
            "",
            "::::",
            "",
        ].join("\n");
        const document = makeDocument(content);

        // @ts-expect-error protected
        const areas = instance.getInputAreas(document) as Range[];
        expect(areas.length).toBeGreaterThan(2);

        const starts = areas.map(area => document.offsetAt(area.start));

        const expectedOpenOffsets: number[] = [];
        for (let i = 0; (i = content.indexOf(":::input\n", i)) >= 0; i += ":::input\n".length) {
            expectedOpenOffsets.push(i);
        }

        expect(starts).toEqual(expectedOpenOffsets);
        expect(starts).toEqual([...starts].sort((a, b) => a - b));
    });
});

describe("LeanLspClient.isBusy lifecycle", () => {
    const progress = (processing: any[], uri = "file:///test.lean") => ({
        textDocument: { uri, version: 1 },
        processing,
    });

    const processingRange = () => [{
        range: new Range(new Position(1, 0), new Position(2, 0)),
    }];

    it("sets isBusy to true on document changes", () => {
        const instance = makeClient(false);

        // @ts-expect-error protected
        instance.onDocumentChanged();

        expect((instance as any).isBusy).toBe(true);
    });

    it("sets isBusy to true when file progress reports processing", async () => {
        const instance = makeClient(false);
        jest.spyOn(instance as any, "computeInputAreaStatus").mockResolvedValue(undefined);

        // @ts-expect-error protected
        await instance.onFileProgress(progress(processingRange()));

        expect((instance as any).isBusy).toBe(true);
    });

    it("sets isBusy to false when file progress has no processing ranges", async () => {
        const instance = makeClient(true);
        jest.spyOn(instance as any, "computeInputAreaStatus").mockResolvedValue(undefined);

        // @ts-expect-error protected
        await instance.onFileProgress(progress([]));

        expect((instance as any).isBusy).toBe(false);
    });

    it("does not change isBusy for progress notifications of another document", async () => {
        const instance = makeClient(true);
        jest.spyOn(instance as any, "computeInputAreaStatus").mockResolvedValue(undefined);

        // @ts-expect-error protected
        await instance.onFileProgress(progress([], "file:///other.lean"));

        expect((instance as any).isBusy).toBe(true);
    });

    it("clears isBusy when checking completes", async () => {
        const instance = makeClient(true);
        jest.spyOn(instance as any, "computeInputAreaStatus").mockResolvedValue(undefined);

        // @ts-expect-error protected
        await instance.onCheckingCompleted();

        expect((instance as any).isBusy).toBe(false);
    });

    it("does not get stuck busy after edit -> processing -> done sequence", async () => {
        const instance = makeClient(false);
        jest.spyOn(instance as any, "computeInputAreaStatus").mockResolvedValue(undefined);

        // @ts-expect-error protected
        instance.onDocumentChanged();
        expect((instance as any).isBusy).toBe(true);

        // @ts-expect-error protected
        await instance.onFileProgress(progress(processingRange()));
        expect((instance as any).isBusy).toBe(true);

        // @ts-expect-error protected
        await instance.onCheckingCompleted();
        expect((instance as any).isBusy).toBe(false);
    });
});