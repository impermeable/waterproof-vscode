/**
 * The proof status of an input area.
 */
export enum InputAreaStatus {
    /** The proof is correct. */
    Proven = "proven",
    /** The proof is unfinished or contains an error. */
    Incomplete = "incomplete",
    /** The input area does not contain `Qed.` at the end, so the status cannot be determined. */
    Invalid = "invalid",
    /** Not in view, so was not requested */
    NotInView = "not-in-view",
}