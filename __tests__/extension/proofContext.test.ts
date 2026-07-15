// Unit tests for the `proofContext` method on the Waterproof extension class.
//
// LLM-generated tests that might encode existing faulty behaviour.
//
// `proofContext` is a plain prototype method, so we exercise it in isolation by
// invoking it with a hand-rolled `this` context (`Waterproof.prototype
// .proofContext.call(fakeThis, ...)`) instead of constructing the full
// extension, which would pull in the entire VS Code activation path.
//
// The document is modelled from a real source string so that
// getText/offsetAt/positionAt stay mutually consistent and the tests exercise
// the actual regex + offset arithmetic.

jest.mock(
  "vscode",
  () => ({
    Position: class {
      constructor(
        public line: number,
        public character: number,
      ) {}
      isBefore(other: { line: number; character: number }) {
        return (
          this.line < other.line ||
          (this.line === other.line && this.character < other.character)
        );
      }
    },
    Range: class {
      constructor(
        public start: unknown,
        public end: unknown,
      ) {}
    },
    commands: {
      registerCommand: jest.fn(),
      registerTextEditorCommand: jest.fn(),
      executeCommand: jest.fn(),
    },
    window: {
      createOutputChannel: jest.fn(() => ({
        appendLine: jest.fn(),
        dispose: jest.fn(),
      })),
    },
    workspace: {},
    ConfigurationTarget: { Global: 1 },
    Uri: { parse: jest.fn(), joinPath: jest.fn() },
    RevealOutputChannelOn: { Info: 1 },
  }),
  { virtual: true },
);

jest.mock(
  "vscode-languageclient",
  () => ({
    RevealOutputChannelOn: { Info: 1 },
  }),
  { virtual: true },
);

// extension.ts imports a large collaborator graph; everything below is mocked so
// the module loads cheaply. Mirrors the setup in eventHandlers.test.ts.
jest.mock("../../src/lsp-client/commandExecutor", () => ({
  executeCommand: jest.fn(),
  executeCommandFullOutput: jest.fn(),
}));
jest.mock("../../src/helpers", () => ({
  WaterproofLogger: { log: jest.fn(), debug: jest.fn(), show: jest.fn() },
  WaterproofConfigHelper: {
    get: jest.fn(),
    update: jest.fn(),
    configuration: {},
  },
  WaterproofFileUtil: {},
  WaterproofPackageJSON: {},
  WaterproofSetting: {},
}));
jest.mock("../../src/pm-editor", () => ({
  WaterproofEditorProvider: { register: jest.fn() },
}));
jest.mock("../../src/util", () => ({
  checkConflictingExtensions: jest.fn(),
  excludeRocqFileTypes: jest.fn(),
  checkTrimmingWhitespace: jest.fn(),
}));
jest.mock("../../src/components/enableButton", () => ({
  WaterproofStatusBar: class {},
}));
jest.mock("../../src/webviews/sidePanel", () => ({
  addSidePanel: jest.fn(),
  SidePanelProvider: class {},
}));
jest.mock("../../src/webviews/standardviews/search", () => ({
  Search: class {},
}));
jest.mock("../../src/webviews/standardviews/execute", () => ({
  ExecutePanel: class {},
}));
jest.mock("../../src/webviews/standardviews/symbols", () => ({
  SymbolsPanel: class {},
}));
jest.mock("../../src/webviews/standardviews/tactics", () => ({
  TacticsPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/debug", () => ({
  DebugPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/goalsPanel", () => ({
  GoalsPanel: class {},
}));
jest.mock("../../src/webviews/goalviews/compositeGoalsPanel", () => ({
  CompositeGoalsPanel: class {},
}));
jest.mock("../../src/lsp-client/composite", () => ({
  CompositeClient: class {},
}));
jest.mock("../../src/lsp-client/rocq", () => ({
  RocqLspServerConfig: { create: jest.fn() },
}));
jest.mock("../../src/lsp-client/lean", () => ({
  LeanLspServerConfig: { create: jest.fn() },
}));
jest.mock("../../src/helpers/exerciseSheet", () => ({
  clearInputCells: jest.fn(),
}));

import { Position } from "vscode";
import { Waterproof } from "../../src/extension";

type Sym = {
  name: string;
  range: { start: { line: number; character: number } };
};

/**
 * Minimal text-backed stand-in for a VS Code `TextDocument`. `\n` separates
 * lines; offsetAt/positionAt are exact inverses for in-bounds positions.
 */
function makeDocument(text: string) {
  const lineStarts = [0];
  for (let i = 0; i < text.length; i++) {
    if (text[i] === "\n") lineStarts.push(i + 1);
  }
  return {
    uri: { toString: () => "file:///proof.v" },
    version: 1,
    getText: () => text,
    offsetAt: (pos: { line: number; character: number }) => {
      const base = lineStarts[pos.line] ?? text.length;
      return base + pos.character;
    },
    positionAt: (offset: number) => {
      let line = 0;
      for (let i = 0; i < lineStarts.length; i++) {
        if (lineStarts[i] <= offset) line = i;
        else break;
      }
      return new Position(line, offset - lineStarts[line]);
    },
  };
}

type Ctx = {
  client: {
    activeDocument: unknown;
    activeCursorPosition: unknown;
    requestSymbols: jest.Mock;
  };
};

function makeCtx(
  document: unknown,
  cursor: unknown,
  symbols: Sym[],
): Ctx {
  return {
    client: {
      activeDocument: document,
      activeCursorPosition: cursor,
      requestSymbols: jest.fn(async () => symbols),
    },
  };
}

const proofContext = (
  Waterproof.prototype as unknown as {
    proofContext: (
      this: unknown,
      cursorMarker?: string,
    ) => Promise<{
      name: string;
      full: string;
      withCursorMarker: string;
      proofRange: { start: unknown; end: unknown };
    }>;
  }
).proofContext;

// A document with two lemmas so we can test lemma selection as well as the
// happy-path extraction.
const SOURCE = [
  "Lemma foo : True.", // line 0
  "Proof.", // line 1
  "exact I.", // line 2
  "Qed.", // line 3
  "", // line 4
  "Lemma bar : 1 = 1.", // line 5
  "Proof.", // line 6
  "reflexivity.", // line 7
  "Qed.", // line 8
  "", // line 9 (trailing newline)
].join("\n");

const SYMBOLS: Sym[] = [
  { name: "foo", range: { start: { line: 0, character: 0 } } },
  { name: "bar", range: { start: { line: 5, character: 0 } } },
];

describe("Waterproof.proofContext", () => {
  describe("happy path", () => {
    it("extracts the lemma the cursor is inside, with whitespace collapsed", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, new Position(7, 0), SYMBOLS);

      const result = await proofContext.call(ctx);

      expect(result.name).toBe("bar");
      expect(result.full).toBe("Lemma bar : 1 = 1. Proof. reflexivity. Qed. ");
    });

    it("inserts the default cursor marker at the cursor offset", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, new Position(7, 0), SYMBOLS);

      const result = await proofContext.call(ctx);

      expect(result.withCursorMarker).toBe(
        "Lemma bar : 1 = 1. Proof. {!* CURSOR *!}reflexivity. Qed. ",
      );
    });

    it("honours a custom cursor marker", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, new Position(7, 0), SYMBOLS);

      const result = await proofContext.call(ctx, "<HERE>");

      expect(result.withCursorMarker).toBe(
        "Lemma bar : 1 = 1. Proof. <HERE>reflexivity. Qed. ",
      );
    });

    it("returns a proofRange from the end of `Proof.` to the start of the closer", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, new Position(7, 0), SYMBOLS);

      const result = await proofContext.call(ctx);

      const barIdx = SOURCE.indexOf("Lemma bar");
      const expectedStart =
        SOURCE.indexOf("Proof.", barIdx) + "Proof.".length;
      const expectedEnd = SOURCE.indexOf("Qed.", barIdx);

      expect(result.proofRange.start).toEqual(doc.positionAt(expectedStart));
      expect(result.proofRange.end).toEqual(doc.positionAt(expectedEnd));
    });

    it("selects the nearest lemma before the cursor when several exist", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, new Position(2, 0), SYMBOLS);

      const result = await proofContext.call(ctx);

      expect(result.name).toBe("foo");
      expect(result.full).toBe("Lemma foo : True. Proof. exact I. Qed. ");
    });
  });

  describe("marker / fence stripping", () => {
    it("removes input-area tags and coq code fences", async () => {
      const text = [
        "Lemma baz : True.",
        "Proof.",
        "<input-area>",
        "```coq",
        "exact I.",
        "```",
        "</input-area>",
        "Qed.",
        "",
      ].join("\n");
      const doc = makeDocument(text);
      const ctx = makeCtx(doc, new Position(4, 0), [
        { name: "baz", range: { start: { line: 0, character: 0 } } },
      ]);

      const result = await proofContext.call(ctx);

      expect(result.full).not.toMatch(/input-area/);
      expect(result.full).not.toMatch(/```/);
      expect(result.full).toBe("Lemma baz : True. Proof. exact I. Qed. ");
    });
  });

  describe("error handling", () => {
    it("throws when there is no active document", async () => {
      const ctx = makeCtx(undefined, new Position(7, 0), SYMBOLS);
      await expect(proofContext.call(ctx)).rejects.toThrow(
        "No active document or cursor position",
      );
    });

    it("throws when there is no cursor position", async () => {
      const doc = makeDocument(SOURCE);
      const ctx = makeCtx(doc, undefined, SYMBOLS);
      await expect(proofContext.call(ctx)).rejects.toThrow(
        "No active document or cursor position",
      );
    });

    it("throws when no lemma symbol precedes the cursor", async () => {
      const doc = makeDocument(SOURCE);
      // Cursor before every symbol.
      const ctx = makeCtx(doc, new Position(0, 0), SYMBOLS);
      await expect(proofContext.call(ctx)).rejects.toThrow(
        "Could not find lemma before cursor",
      );
    });

    it("throws when the proof has no Qed/Admitted/Defined closer", async () => {
      const text = ["Lemma open : True.", "Proof.", "exact I.", ""].join("\n");
      const doc = makeDocument(text);
      const ctx = makeCtx(doc, new Position(2, 0), [
        { name: "open", range: { start: { line: 0, character: 0 } } },
      ]);
      await expect(proofContext.call(ctx)).rejects.toThrow(
        "Could not find end of proof",
      );
    });

    it("throws when the lemma keyword is not recognised", async () => {
      // `Example` is not in the accepted keyword list, so the start regex
      // fails even though a closer is present.
      const text = ["Example ex : True.", "Proof.", "exact I.", "Qed.", ""].join(
        "\n",
      );
      const doc = makeDocument(text);
      const ctx = makeCtx(doc, new Position(2, 0), [
        { name: "ex", range: { start: { line: 0, character: 0 } } },
      ]);
      await expect(proofContext.call(ctx)).rejects.toThrow(
        "Could not find start of proof",
      );
    });
  });

  describe("known breakage: statement contains an internal period", () => {
    // The start regex consumes the statement body with `[^.]*`, which stops at
    // the FIRST period. A statement containing an internal period -- e.g. a
    // qualified name like `Nat.add` -- therefore fails to match, even though it
    // is a perfectly valid lemma. This test documents that limitation; see the
    // NOTE on `startRegex` in src/extension.ts. It is expected to fail (throw)
    // and would need to change if the regex is ever fixed.
    it("throws on a valid lemma whose statement uses a qualified name", async () => {
      const text = [
        "Lemma bar : Nat.add 0 0 = 0.",
        "Proof.",
        "reflexivity.",
        "Qed.",
        "",
      ].join("\n");
      const doc = makeDocument(text);
      const ctx = makeCtx(doc, new Position(2, 0), [
        { name: "bar", range: { start: { line: 0, character: 0 } } },
      ]);

      await expect(proofContext.call(ctx)).rejects.toThrow(
        "Could not find start of proof",
      );
    });
  });
});
