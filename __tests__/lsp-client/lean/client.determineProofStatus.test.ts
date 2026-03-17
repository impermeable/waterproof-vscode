jest.mock("vscode", () => {
    const Position = class {
        constructor(public line: number, public character: number) {}
        translate(lineDelta: number, charDelta: number) {
            return new Position(this.line + lineDelta, this.character + charDelta);
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
jest.mock("../../helpers",          () => ({
    WaterproofConfigHelper: { get: jest.fn(() => false) },
    WaterproofLogger:       { log: jest.fn(), debug: jest.fn() },
    WaterproofSetting:      {},
    qualifiedSettingName:   jest.fn(s => s),
}), { virtual: true });
jest.mock("../sentenceManager",     () => ({ SentenceManager: class { onProgress() {} dispose() {} } }), { virtual: true });
jest.mock("../clientTypes",         () => ({}), { virtual: true });
jest.mock("../requestTypes",        () => ({ convertToSimple: jest.fn() }), { virtual: true });
jest.mock("../qedStatus",           () => ({ findOccurrences: jest.fn(() => []) }), { virtual: true });
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