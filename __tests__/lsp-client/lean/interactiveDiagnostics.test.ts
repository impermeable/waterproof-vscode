import { readFileSync } from "fs";
import { join } from "path";
import type {
  InteractiveDiagnostic,
  MsgEmbed,
  TaggedText,
} from "@leanprover/infoview-api";
import {
  collectRpcRefs,
  flattenMessage,
  toSegments,
  toSegmentedDiagnostics,
} from "../../../src/lsp-client/lean/interactiveDiagnostics";

// Recorded from a Lean v4.31.0 server started with `hasWidgets: true`, for a file with two
// Verbose Lean `help h` calls (on lines 3 and 7). `published` holds the plain diagnostics the
// server published for the same file.
const fixture: {
  published: { range: unknown; message: string }[];
  interactive: InteractiveDiagnostic[];
} = JSON.parse(
  readFileSync(
    join(__dirname, "fixtures", "help-interactive-diagnostics.json"),
    "utf8",
  ),
);

const range = (line: number, start: number, end: number) => ({
  start: { line, character: start },
  end: { line, character: end },
});

const suggestionWidget = (
  suggestion: string,
  alt: TaggedText<MsgEmbed>,
  id = "Lean.Meta.Hint.textInsertionWidget",
): TaggedText<MsgEmbed> => ({
  tag: [
    {
      widget: {
        wi: {
          id,
          javascriptHash: "0",
          props: { range: range(3, 2, 8), suggestion },
        },
        alt,
      },
    } as MsgEmbed,
    { text: "" },
  ],
});

describe("flattenMessage", () => {
  it("reproduces the published message for every recorded diagnostic", () => {
    expect(fixture.interactive).toHaveLength(fixture.published.length);
    for (const d of fixture.interactive) {
      const flat = flattenMessage(d.message);
      expect(
        fixture.published.some(
          (p) =>
            JSON.stringify(p.range) === JSON.stringify(d.range) &&
            p.message === flat,
        ),
      ).toBe(true);
    }
  });

  it("takes the text of an expr embed from the embed, not from the tagged text", () => {
    const message: TaggedText<MsgEmbed> = {
      append: [
        { text: "a " },
        { tag: [{ expr: { text: "x + 1" } } as MsgEmbed, { text: "" }] },
      ],
    };

    expect(flattenMessage(message)).toBe("a x + 1");
  });
});

describe("toSegments", () => {
  it("turns each recorded help suggestion into a segment with its edit", () => {
    const segments = toSegments(fixture.interactive[1].message);

    expect(segments.filter((s) => s.edit)).toEqual([
      {
        text: "Since ∀ (n : ℕ), P n ⇒ Q n we get that P n₀ ⇒ Q n₀",
        edit: {
          range: range(7, 2, 8),
          newText: "Since ∀ (n : ℕ), P n ⇒ Q n we get that P n₀ ⇒ Q n₀",
        },
      },
      {
        text: "We apply h to n₀",
        edit: { range: range(7, 2, 8), newText: "We apply h to n₀" },
      },
    ]);
    expect(segments.map((s) => s.text).join("")).toBe(
      flattenMessage(fixture.interactive[1].message),
    );
  });

  it("merges adjacent plain segments and drops empty ones", () => {
    const segments = toSegments({
      append: [{ text: "Try " }, { text: "" }, { text: "this: " }],
    });

    expect(segments).toEqual([{ text: "Try this: " }]);
  });

  it("uses the widget's alt text as the segment text", () => {
    // Core Lean's link text is `[apply]`, followed by the suggestion outside the widget.
    const segments = toSegments({
      append: [
        { text: "Try this:\n" },
        suggestionWidget("exact h", { text: "[apply]" }),
        { text: " exact h" },
      ],
    });

    expect(segments).toEqual([
      { text: "Try this:\n" },
      {
        text: "[apply]",
        edit: { range: range(3, 2, 8), newText: "exact h" },
      },
      { text: " exact h" },
    ]);
  });

  it("recognises the diff widget", () => {
    const segments = toSegments(
      suggestionWidget(
        "simp",
        { text: "simp" },
        "Lean.Meta.Hint.tryThisDiffWidget",
      ),
    );

    expect(segments).toEqual([
      { text: "simp", edit: { range: range(3, 2, 8), newText: "simp" } },
    ]);
  });

  it("treats other widgets as plain text", () => {
    const segments = toSegments(
      suggestionWidget("exact h", { text: "exact h" }, "Some.Other.widget"),
    );

    expect(segments).toEqual([{ text: "exact h" }]);
  });

  it("treats a suggestion widget without a range as plain text", () => {
    const message: TaggedText<MsgEmbed> = {
      tag: [
        {
          widget: {
            wi: {
              id: "Lean.Meta.Hint.textInsertionWidget",
              javascriptHash: "0",
              props: { suggestion: "exact h" },
            },
            alt: { text: "exact h" },
          },
        } as MsgEmbed,
        { text: "" },
      ],
    };

    expect(toSegments(message)).toEqual([{ text: "exact h" }]);
  });
});

describe("toSegmentedDiagnostics", () => {
  it("keeps only the recorded help diagnostics, not the linter warnings on the same range", () => {
    const result = toSegmentedDiagnostics(fixture.interactive);

    expect(result.map((d) => d.range)).toEqual([
      range(3, 2, 8),
      range(7, 2, 8),
    ]);
    expect(result.map((d) => d.segments.filter((s) => s.edit).length)).toEqual([
      1, 2,
    ]);
    expect(result[0].message).toBe(fixture.published[0].message);
  });
});

describe("collectRpcRefs", () => {
  it("finds nested references", () => {
    const refs = collectRpcRefs({
      tag: [
        { expr: { tag: [{ info: { p: "1" } }, { text: "x" }] } },
        { append: [{ tag: [{ info: { p: "2" } }, { text: "" }] }] },
      ],
    });

    expect(refs).toEqual([{ p: "1" }, { p: "2" }]);
  });

  it("finds none in the recorded help diagnostics", () => {
    expect(collectRpcRefs(fixture.interactive)).toEqual([]);
  });
});
