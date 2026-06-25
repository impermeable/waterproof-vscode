import { describe, expect, it, jest } from "@jest/globals";

jest.mock(
  "vscode",
  () => ({
    DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2, Hint: 3 },
    Range: class {
      constructor(
        public start: unknown,
        public end: unknown,
      ) {}
    },
    Position: class {
      constructor(
        public line: number,
        public character: number,
      ) {}
    },
  }),
  { virtual: true },
);

jest.mock(
  "vscode-languageclient/lib/common/utils/async",
  () => ({
    map: <T, U>(items: T[], fn: (item: T) => U): U[] => items.map(fn),
  }),
  { virtual: true },
);

jest.mock("./requestTypes", () => ({}), { virtual: true });

jest.mock(
  "vscode-languageclient",
  () => {
    const DiagnosticSeverity = {
      Error: 0,
      Warning: 1,
      Information: 2,
      Hint: 3,
    };
    return {
      DiagnosticSeverity,
      Protocol2CodeConverter: {},
      Code2ProtocolConverter: {},
    };
  },
  { virtual: true },
);

import {
  Code2ProtocolConverter,
  DiagnosticSeverity,
  Protocol2CodeConverter,
} from "vscode-languageclient";
import { patchDiagnosticConverters } from "../../../src/lsp-client/lean/converter";

interface LspRange {
  start: { line: number; character: number };
  end: { line: number; character: number };
}

interface TestDiagnostic {
  message: string;
  severity: DiagnosticSeverity;
  range: LspRange;
  fullRange?: LspRange;
  leanTags?: number[];
  isSilent?: boolean;
}

const FULL_RANGE: LspRange = {
  start: { line: 0, character: 0 },
  end: { line: 99, character: 0 },
};

const EMPTY_RANGE: LspRange = {
  start: { line: 0, character: 0 },
  end: { line: 0, character: 0 },
};

interface TestP2C {
  asDiagnostic: (protDiag: TestDiagnostic, token?: unknown) => TestDiagnostic;
  asDiagnostics: (
    diags: TestDiagnostic[],
    token?: unknown,
  ) => Promise<TestDiagnostic[]>;
  asRange: (r: LspRange) => LspRange;
}

interface TestC2P {
  asDiagnostic: (diag: TestDiagnostic) => TestDiagnostic;
  asDiagnostics: (diags: TestDiagnostic[]) => Promise<TestDiagnostic[]>;
  asRange: (r: LspRange) => LspRange;
}

/**
 * Shifts every line number up by one. Used as p2c.asRange so that tests can
 * distinguish "the value came through asRange" from "the raw range was copied".
 * Captured before patching so comparisons use the original transform, not
 * whatever the patched converter exposes.
 */
function shiftedRange(r: LspRange): LspRange {
  return {
    start: { line: r.start.line + 1, character: r.start.character },
    end: { line: r.end.line + 1, character: r.end.character },
  };
}

function makeP2C(overrides = {}): TestP2C & Protocol2CodeConverter {
  const base: TestP2C = {
    asDiagnostic: jest.fn(
      (protDiag: TestDiagnostic): TestDiagnostic => ({
        message: protDiag.message,
        severity: protDiag.severity,
        range: protDiag.range,
      }),
    ),
    asDiagnostics: jest.fn(
      async (diags: TestDiagnostic[]): Promise<TestDiagnostic[]> =>
        diags.map((d) => ({
          message: d.message,
          severity: d.severity,
          range: d.range,
        })),
    ),
    asRange: jest.fn(shiftedRange),
  };
  return { ...base, ...overrides } as TestP2C & Protocol2CodeConverter;
}

function makeC2P(overrides = {}): TestC2P & Code2ProtocolConverter {
  const base: TestC2P = {
    asDiagnostic: jest.fn(
      (diag: TestDiagnostic): TestDiagnostic => ({
        message: diag.message,
        severity: diag.severity,
        range: diag.range,
      }),
    ),
    asDiagnostics: jest.fn(
      async (diags: TestDiagnostic[]): Promise<TestDiagnostic[]> =>
        diags.map((d) => ({
          message: d.message,
          severity: d.severity,
          range: d.range,
        })),
    ),
    asRange: jest.fn((r: LspRange): LspRange => r),
  };
  return { ...base, ...overrides } as TestC2P & Code2ProtocolConverter;
}

function makeDiag(overrides: Partial<TestDiagnostic> = {}): TestDiagnostic {
  return {
    message: "err",
    severity: DiagnosticSeverity.Error,
    range: EMPTY_RANGE,
    fullRange: EMPTY_RANGE,
    ...overrides,
  };
}

describe("patchDiagnosticConverters", () => {
  describe("p2c.asDiagnostic (patched)", () => {
    it("sets fullRange on the result to the output of asRange, not the raw input range", () => {
      const p2c = makeP2C();
      const c2p = makeC2P();
      patchDiagnosticConverters(p2c, c2p);

      const result = p2c.asDiagnostic(makeDiag({ fullRange: FULL_RANGE }));

      // shiftedRange is the pre-patch asRange transform; the patched converter
      // must use asRange rather than copying the input range verbatim.
      expect(result.fullRange).toStrictEqual(shiftedRange(FULL_RANGE));
    });

    it("copies leanTags onto the returned diagnostic", () => {
      const p2c = makeP2C();
      const c2p = makeC2P();
      patchDiagnosticConverters(p2c, c2p);

      const tags = [1];
      const result = p2c.asDiagnostic(makeDiag({ leanTags: tags }));

      expect(result.leanTags).toEqual(tags);
    });

    it("copies isSilent onto the returned diagnostic", () => {
      const p2c = makeP2C();
      const c2p = makeC2P();
      patchDiagnosticConverters(p2c, c2p);

      const result = p2c.asDiagnostic(makeDiag({ isSilent: true }));

      expect(result.isSilent).toBe(true);
    });

    it("returns a diagnostic with a non-empty message when the original message is empty", () => {
      const p2c = makeP2C();
      const c2p = makeC2P();
      patchDiagnosticConverters(p2c, c2p);

      const result = p2c.asDiagnostic(makeDiag({ message: "" }));

      expect(result.message).not.toBe("");
    });

    it("leaves a non-empty message unchanged", () => {
      const p2c = makeP2C();
      const c2p = makeC2P();
      patchDiagnosticConverters(p2c, c2p);

      const diag = makeDiag({ message: "real error" });
      p2c.asDiagnostic(diag);

      expect(diag.message).toBe("real error");
    });

    describe("p2c.asDiagnostics (patched)", () => {
      it("maps each item through the patched asDiagnostic", async () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const tags = [1];
        const diags = [
          makeDiag({
            message: "a",
            leanTags: tags,
            fullRange: FULL_RANGE,
            isSilent: false,
          }),
          makeDiag({
            message: "b",
            severity: DiagnosticSeverity.Warning,
            leanTags: [],
            fullRange: FULL_RANGE,
            isSilent: true,
          }),
        ];

        const results = await p2c.asDiagnostics(diags, undefined);

        expect(results).toHaveLength(2);
        expect(results[0].leanTags).toEqual(tags);
        expect(results[1].isSilent).toBe(true);
      });
    });

    describe("c2p.asDiagnostic (patched)", () => {
      it("sets fullRange on the result to the output of asRange, not the raw input range", () => {
        // Give c2p.asRange the same shifted transform as p2c so we can tell
        // whether the result came through asRange or was copied verbatim.
        const c2p = makeC2P({ asRange: jest.fn(shiftedRange) });
        const p2c = makeP2C();
        patchDiagnosticConverters(p2c, c2p);

        const result = c2p.asDiagnostic(makeDiag({ fullRange: FULL_RANGE }));

        expect(result.fullRange).toStrictEqual(shiftedRange(FULL_RANGE));
      });

      it("copies leanTags onto the protocol diagnostic", () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const tags = [1];
        const result = c2p.asDiagnostic(makeDiag({ leanTags: tags }));

        expect(result.leanTags).toEqual(tags);
      });

      it("copies isSilent onto the protocol diagnostic", () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const result = c2p.asDiagnostic(makeDiag({ isSilent: true }));

        expect(result.isSilent).toBe(true);
      });

      it("preserves isSilent: false without coercing it to undefined", () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const result = c2p.asDiagnostic(makeDiag({ isSilent: false }));

        expect(result.isSilent).toBe(false);
      });

      it("still forwards the base fields via the original converter", () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const result = c2p.asDiagnostic(makeDiag({ message: "base message" }));

        expect(result.message).toBe("base message");
      });
    });

    describe("c2p.asDiagnostics (patched)", () => {
      it("maps each item through the patched asDiagnostic", async () => {
        const p2c = makeP2C();
        const c2p = makeC2P();
        patchDiagnosticConverters(p2c, c2p);

        const diags = [
          makeDiag({
            message: "x",
            leanTags: [1],
            fullRange: FULL_RANGE,
            isSilent: false,
          }),
          makeDiag({
            message: "y",
            leanTags: [],
            fullRange: FULL_RANGE,
            isSilent: true,
          }),
        ];

        const results = await c2p.asDiagnostics(diags);

        expect(results).toHaveLength(2);
        expect(results[0].leanTags).toEqual([1]);
        expect(results[1].isSilent).toBe(true);
      });
    });
  });
});
