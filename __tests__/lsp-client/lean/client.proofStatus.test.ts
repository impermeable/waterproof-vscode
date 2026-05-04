// These tests focus on logic related to determining the proof status of an input area in the LeanLspClient.
// These include the main logic of determineProofStatus, which combines diagnostic information and goal responses to classify an input area as Correct, Incorrect, or Invalid.
// We also test the `getInputAreas` and `this.isBusy` logic since it is a key dependency of determineProofStatus, and the proof status logic relies on the areas being returned in document order.
// The tests use a lot of mocking and test doubles since we want to isolate the logic of determineProofStatus and not depend on the full behavior of the LanguageClient or actual LSP communication.

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
        isBeforeOrEqual(other: InstanceType<typeof Position>) {
            return !this.isAfter(other);
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

jest.mock("@impermeable/waterproof-editor", () => ({
    InputAreaStatus: { Correct: "Correct", Incorrect: "Incorrect", Invalid: "Invalid" },
}), { virtual: true });
jest.mock("@leanprover/infoview-api", () => ({}), { virtual: true });
jest.mock("../../../src/lsp-client/lean/converter", () => ({ patchDiagnosticConverters: jest.fn() }), { virtual: true });

import { Range, Position, DiagnosticSeverity } from "vscode";
import { InputAreaStatus } from "@impermeable/waterproof-editor";
import { LeanLspClient } from "../../../src/lsp-client/lean/client";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
const INPUT_AREA   = new Range(new Position(2, 0), new Position(6, 0));
const LOWER_BOUND  = new Position(2, 0);

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

const call = (
    instance:   LeanLspClient,
    diags:      any[]    = [],
    area:       Range    = INPUT_AREA,
    lower:      Position = LOWER_BOUND,
) => (instance as any).determineProofStatus(FAKE_DOCUMENT, area, diags, lower);

/** Creates a diagnostic with a given line range and severity. */
const diag = (startLine: number, endLine: number, severity: number) => ({
    message:  "test",
    severity,
    range: new Range(new Position(startLine, 0), new Position(endLine, 0)),
});

/** Creates a diagnostic with a specific message (used for sorry / hint tests). */
const msgDiag = (message: string, line: number, character = 0) => ({
    message,
    severity: DiagnosticSeverity.Warning,      // severity is irrelevant for message checks
    range: new Range(new Position(line, character), new Position(line, character)),
});

function makeDocument(content: string) {
    const lines = content.split("\n");
 
    const positionAt = (offset: number): { line: number; character: number } => {
        let remaining = offset;
        for (let i = 0; i < lines.length; i++) {
            // +1 for the newline that split() consumed
            const lineLen = lines[i].length + 1;
            if (remaining < lineLen) return new Position(i, remaining);
            remaining -= lineLen;
        }
        // offset == content.length → end of last line
        return new Position(lines.length - 1, lines[lines.length - 1].length);
    };
 
    const offsetAt = (pos: { line: number; character: number }): number => {
        let offset = 0;
        for (let i = 0; i < pos.line; i++) offset += lines[i].length + 1;
        return offset + pos.character;
    };
 
    return {
        ...FAKE_DOCUMENT,
        getText:    () => content,
        lineCount:  lines.length,
        positionAt,
        offsetAt,
    } as any;
}

function posOf(content: string, needle: string, fromOffset = 0) {
    const idx = content.indexOf(needle, fromOffset);
    if (idx === -1) throw new Error(`"${needle}" not found after offset ${fromOffset}`);
    const before = content.slice(0, idx);
    const line = before.split("\n").length - 1;
    const character = idx - before.lastIndexOf("\n") - 1;
    return { line, character, offset: idx };
}

 

// ===========================================================================
// Tests
// ===========================================================================
describe("LeanLspClient.determineProofStatus", () => {

    // ---- busy guard --------------------------------------------------------

    it("returns Incorrect immediately when isBusy is true (no goal request made)", async () => {
        const instance = makeClient(true);
        const requestGoals = jest.spyOn(instance, "requestGoals" as any);

        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
        expect(requestGoals).not.toHaveBeenCalled();
    });

    // ---- error diagnostics -------------------------------------------------

    it("returns Incorrect when there is an Error diagnostic fully inside the area", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        expect(await call(instance, [diag(3, 5, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect when an Error diagnostic overlaps the area boundary", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        // range [5,7] intersects area [2,6]
        expect(await call(instance, [diag(5, 7, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Incorrect);
    });

    it("ignores an Error diagnostic that lies entirely outside the area", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        expect(await call(instance, [diag(10, 12, DiagnosticSeverity.Error)])).toBe(InputAreaStatus.Correct);
    });

    it("does not treat Warning, Information, or Hint diagnostics as blocking", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        expect(await call(instance, [
            diag(3, 4, DiagnosticSeverity.Warning),
            diag(4, 5, DiagnosticSeverity.Information),
            diag(5, 6, DiagnosticSeverity.Hint),
        ])).toBe(InputAreaStatus.Correct);
    });

    // ---- goal response -----------------------------------------------------

    it("returns Incorrect when the goals response is null", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue(null);

        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect when the goals response is undefined", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue(undefined);

        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Incorrect when the goals array is non-empty", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [{ type: "⊢ False" }] });
        expect(await call(instance)).toBe(InputAreaStatus.Incorrect);
    });

    it("returns Correct when idle, no errors, and goals are empty", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance)).toBe(InputAreaStatus.Correct);
    });

    // ---- sorry detection (Invalid) -----------------------------------------

    it("returns Invalid when goals are empty but a sorry diagnostic is inside the area", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        // line 4 is strictly inside [lowerBound=2, areaEnd=6]
        expect(await call(instance, [msgDiag("declaration uses 'sorry'", 4)])).toBe(InputAreaStatus.Invalid);
    });

    it("returns Correct when a sorry diagnostic sits exactly on lowerBound (not strictly after)", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        // line 2 == lowerBound.line, character 0 == lowerBound.character → not after → ignored
        expect(await call(instance, [msgDiag("declaration uses 'sorry'", 2, 0)])).toBe(InputAreaStatus.Correct);
    });

    it("returns Correct when a sorry diagnostic is after the area end", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        // line 7 > area end line 6
        expect(await call(instance, [msgDiag("declaration uses 'sorry'", 7)])).toBe(InputAreaStatus.Correct);
    });

    it("returns Correct when a non-sorry message matches neither sorry nor hints", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        expect(await call(instance, [msgDiag("type mismatch", 4)])).toBe(InputAreaStatus.Correct);
    });

    // ---- interaction between error diags and sorry -------------------------

    it("returns Incorrect (not Invalid) when there is both an Error diag and a sorry diag in the area", async () => {
        const instance = makeClient();
        // requestGoals should not even be reached when an error diag is present
        const requestGoals = jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });

        const result = await call(instance, [
            diag(3, 5, DiagnosticSeverity.Error),
            msgDiag("declaration uses 'sorry'", 4),
        ]);

        expect(result).toBe(InputAreaStatus.Incorrect);
        expect(requestGoals).not.toHaveBeenCalled();
    });

    it("returns Invalid when a sorry diagnostic sits exactly on inputArea.end (isBeforeOrEqual includes the boundary)", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        expect(await call(instance, [msgDiag("declaration uses 'sorry'", 6, 0)])).toBe(InputAreaStatus.Invalid);
    });

    it("returns Correct when a 'declaration uses sorry' diagnostic is Information severity (not Warning), prevents the user from doing: \"#check declaration uses 'sorry'\"", async () => {
        const instance = makeClient();
        jest.spyOn(instance, "requestGoals" as any).mockResolvedValue({ goals: [] });
        
        const infoSorryDiag = {
            message:  "declaration uses 'sorry'",
            severity: DiagnosticSeverity.Information,
            range: new Range(new Position(4, 0), new Position(4, 0)),
        };
    
        expect(await call(instance, [infoSorryDiag])).toBe(InputAreaStatus.Correct);
    });
});

// The most important test is the order in which the input areas are returned, since the proof status logic assumes they are in document order. 
// The other tests just verify that the getInputAreas logic correctly identifies the start and end of input areas in various scenarios.
describe("LeanLspClient.getInputAreas", () => {
 
    it("returns an empty array when there are no input areas", () => {
        const instance = makeClient();
        const content = "no input areas here\n";
        const document = makeDocument(content);
 
        const areas = (instance as any).getInputAreas(document) as Range[];
 
        expect(areas).toHaveLength(0);
    });
 
    it("returns a single range whose start is the :::input tag and end is the ::: closing tag", () => {
        const instance = makeClient();
        const content = [
            "before",
            ":::input",
            "proof goes here",
            ":::",
            "after",
        ].join("\n");
        const document = makeDocument(content);
 
        const areas = (instance as any).getInputAreas(document) as Range[];
 
        expect(areas).toHaveLength(1);
 
        const openPos  = posOf(content, ":::input\n");
        const closePos = posOf(content, ":::\n");
 
        expect(areas[0].start).toEqual(new Position(openPos.line,  openPos.character));
        expect(areas[0].end  ).toEqual(new Position(closePos.line, closePos.character));
    });
 
    it("correctly locates the closing ::: even when the body contains text", () => {
        const instance = makeClient();
        const content = [
            ":::input",
            "  By h we get x",
            "  We conclude",
            ":::",
            "",
        ].join("\n");
        const document = makeDocument(content);
 
        const areas = (instance as any).getInputAreas(document) as Range[];
 
        expect(areas).toHaveLength(1);
 
        // Start must be line 0 (the :::input line), end must be line 3 (the ::: line)
        expect(areas[0].start.line).toBe(0);
        expect(areas[0].end.line  ).toBe(3);
    });

    it("returns two areas in document order for a file with two input blocks", () => {
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
 
        const areas = (instance as any).getInputAreas(document) as Range[];
 
        expect(areas).toHaveLength(2);
 
        const firstOpen  = posOf(content, ":::input\n");
        const firstClose = posOf(content, ":::\n");
        const secondOpen = posOf(content, ":::input\n", firstOpen.offset + 1);
        const secondClose = posOf(content, ":::\n", firstClose.offset + 1);
 
        // First area
        expect(areas[0].start).toEqual(new Position(firstOpen.line,   firstOpen.character));
        expect(areas[0].end  ).toEqual(new Position(firstClose.line,  firstClose.character));
 
        // Second area
        expect(areas[1].start).toEqual(new Position(secondOpen.line,  secondOpen.character));
        expect(areas[1].end  ).toEqual(new Position(secondClose.line, secondClose.character));
    });
 
    it("each area starts after the previous area ends (areas do not overlap)", () => {
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
 
        for (let i = 1; i < areas.length; i++) {
            const prevEndOffset  = document.offsetAt(areas[i - 1].end);
            const currStartOffset = document.offsetAt(areas[i].start);
            expect(currStartOffset).toBeGreaterThan(prevEndOffset);
        }
    });
 
    it("finds exactly three areas in realistic multilean content at the correct offsets", () => {
        const instance = makeClient();
        const content = [
            "#doc (WaterproofGenre) \"Index\" =>",
            "",
            "::::multilean",
            "",
            "## ATC - 003",
            "```lean",
            "Example \"ATC - 003\"",
            "Proof:",
            "```",
            ":::input",      // line 9  - first open
            "```lean",
            "",
            "```",
            ":::",            // line 13 - first close
            "",
            "## ATC - 009",
            ":::hint \"Show hint\"",
            "  hello",
            ":::",
            "```lean",
            "Example \"ATC - 009\"",
            "Proof:",
            "```",
            ":::input",      // line 23 - second open
            "```lean",
            "",
            "```",
            ":::",            // line 27 - second close
            "",
            "## ATC - 014",
            "```lean",
            "Example \"ATC - 014\"",
            "Proof:",
            "```",
            ":::input",      // line 34 - third open
            "```lean",
            "  Fix ε > 0",
            "```",
            ":::",            // line 38 - third close
            "",
            "::::",
            "",
        ].join("\n");
        const document = makeDocument(content);
 
        // @ts-expect-error protected
        const areas = instance.getInputAreas(document) as Range[];
 
        expect(areas).toHaveLength(3);
 
        // Collect the ground-truth positions by scanning the content string directly
        // so this test does not depend on line-number constants staying in sync with
        // the content array above.
        const openPositions: { line: number; character: number }[] = [];
        const closePositions: { line: number; character: number }[] = [];
 
        let searchFrom = 0;
        while (true) {
            const found = posOf(content, ":::input\n", searchFrom);
            if (found.offset === -1) break;
            openPositions.push({ line: found.line, character: found.character });
            searchFrom = found.offset + ":::input\n".length;
            if (openPositions.length === 3) break;
        }
 
        searchFrom = 0;
        // Each closing ::: comes after its matching :::input; collect them in order
        // by scanning after each open position we already found.
        for (const open of openPositions) {
            const openOffset = document.offsetAt(open);
            const found = posOf(content, ":::\n", openOffset + ":::input\n".length);
            closePositions.push({ line: found.line, character: found.character });
        }
 
        for (let i = 0; i < 3; i++) {
            expect(areas[i].start).toEqual(new Position(openPositions[i].line,  openPositions[i].character));
            expect(areas[i].end  ).toEqual(new Position(closePositions[i].line, closePositions[i].character));
        }
 
        // Sanity: areas are in strictly ascending order
        const startOffsets = areas.map(a => document.offsetAt(a.start));
        expect(startOffsets).toEqual([...startOffsets].sort((a, b) => a - b));
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
});