/**
 * @jest-environment jsdom
 */
import {
  HYPOTHESIS_VISIBILITY_ATTRIBUTE,
  handleHypothesisVisibilityMessage,
  setHypothesisVisibility,
} from "../../views/infoview/hypothesisVisibility";
import { MessageType } from "../../shared";

const attribute = () =>
  document.documentElement.getAttribute(HYPOTHESIS_VISIBILITY_ATTRIBUTE);

afterEach(() => {
  document.documentElement.removeAttribute(HYPOTHESIS_VISIBILITY_ATTRIBUTE);
});

describe("setHypothesisVisibility", () => {
  it("reflects the value onto the document root", () => {
    setHypothesisVisibility("none");
    expect(attribute()).toBe("none");
  });

  it("overwrites a previously set value", () => {
    setHypothesisVisibility("none");
    setHypothesisVisibility("all");
    expect(attribute()).toBe("all");
  });

  it("persists the value through the provided callback", () => {
    const persist = jest.fn();
    setHypothesisVisibility("limited", persist);
    expect(persist).toHaveBeenCalledWith("limited");
  });
});

describe("handleHypothesisVisibilityMessage", () => {
  it("applies and persists a setHypothesisVisibility message", () => {
    const persist = jest.fn();
    const handled = handleHypothesisVisibilityMessage(
      { type: MessageType.setHypothesisVisibility, body: "none" },
      persist,
    );
    expect(handled).toBe(true);
    expect(attribute()).toBe("none");
    expect(persist).toHaveBeenCalledWith("none");
  });

  it("ignores other message types (e.g. Rpc traffic) without touching the DOM", () => {
    const persist = jest.fn();
    const handled = handleHypothesisVisibilityMessage(
      { seqNum: 3, result: {} },
      persist,
    );
    expect(handled).toBe(false);
    expect(attribute()).toBeNull();
    expect(persist).not.toHaveBeenCalled();
  });

  it("ignores a matching type carrying a non-string body", () => {
    const handled = handleHypothesisVisibilityMessage({
      type: MessageType.setHypothesisVisibility,
      body: undefined,
    });
    expect(handled).toBe(false);
    expect(attribute()).toBeNull();
  });

  it("ignores undefined, null and non-object data", () => {
    expect(handleHypothesisVisibilityMessage(undefined)).toBe(false);
    expect(handleHypothesisVisibilityMessage(null)).toBe(false);
    expect(handleHypothesisVisibilityMessage("string")).toBe(false);
    expect(attribute()).toBeNull();
  });
});
