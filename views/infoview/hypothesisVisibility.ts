import { MessageType } from "../../shared";

/**
 * DOM attribute on the infoview root that trim.css keys off to hide the
 * built-in "Tactic state" block. Mirrors the `visibilityOfHypotheses` setting.
 */
export const HYPOTHESIS_VISIBILITY_ATTRIBUTE = "data-wp-hyp-visibility";

/**
 * Reflects the hypothesis-visibility setting onto the document root and persists it through.
 */
export function setHypothesisVisibility(
  value: string,
  persist: (value: string) => void = () => {},
): void {
  document.documentElement.setAttribute(HYPOTHESIS_VISIBILITY_ATTRIBUTE, value);
  persist(value);
}

/**
 * Applies a hypothesis-visibility message from the extension when `data` is one.
 * Returns whether the message was handled.
 */
export function handleHypothesisVisibilityMessage(
  data: unknown,
  persist: (value: string) => void = () => {},
): boolean {
  const message = data as { type?: MessageType; body?: unknown };
  if (
    message?.type === MessageType.setHypothesisVisibility &&
    typeof message.body === "string"
  ) {
    setHypothesisVisibility(message.body, persist);
    return true;
  }
  return false;
}
