// NOTE: These tests were AI-generated. They describe the current behaviour of the code and
// may therefore codify existing buggy behaviour; a failing test is not necessarily a regression.

import { describe, expect, it } from "@jest/globals";
import { applyDocChange, mapDocChange } from "../../src/pm-editor/documentSync";

const change = (startInFile: number, endInFile: number, finalText: string) => ({
  startInFile,
  endInFile,
  finalText,
});

describe("applyDocChange", () => {
  it("applies a single change", () => {
    expect(applyDocChange("abcdef", change(1, 3, "X"))).toBe("aXdef");
  });

  it("applies both edits of a wrapping change in offsets of the original text", () => {
    const wrap = {
      firstEdit: change(1, 1, "<"),
      secondEdit: change(3, 3, ">"),
    };
    expect(applyDocChange("abcdef", wrap)).toBe("a<bc>def");
  });
});

describe("mapDocChange", () => {
  it("leaves changes alone when the texts are equal", () => {
    const c = change(1, 2, "X");
    expect(mapDocChange(c, "abc", "abc")).toBe(c);
  });

  it("leaves changes before the changed range alone", () => {
    expect(mapDocChange(change(0, 1, "X"), "abcdef", "abcZf")).toEqual(
      change(0, 1, "X"),
    );
  });

  it("moves changes after the changed range", () => {
    expect(mapDocChange(change(4, 5, ""), "abcdef", "XYZabcdef")).toEqual(
      change(7, 8, ""),
    );
  });

  it("puts an insertion at an inserted range before it", () => {
    expect(mapDocChange(change(3, 3, "!"), "abcdef", "abcXYdef")).toEqual(
      change(3, 3, "!"),
    );
  });

  it("returns undefined for changes overlapping the changed range", () => {
    expect(mapDocChange(change(3, 4, ""), "abcdef", "abZef")).toBeUndefined();
  });

  it("returns undefined for a wrapping change when one edit conflicts", () => {
    const wrap = {
      firstEdit: change(0, 0, "<"),
      secondEdit: change(3, 3, ">"),
    };
    expect(mapDocChange(wrap, "abcdef", "abZef")).toBeUndefined();
  });

  it("maps both edits of a wrapping change around the changed range", () => {
    const wrap = {
      firstEdit: change(0, 0, "<"),
      secondEdit: change(6, 6, ">"),
    };
    expect(mapDocChange(wrap, "abcdef", "abXYZcdef")).toEqual({
      firstEdit: change(0, 0, "<"),
      secondEdit: change(9, 9, ">"),
    });
  });
});
