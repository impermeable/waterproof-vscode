import { Position, TextDocument } from "vscode";
import { RunResult } from "./lsp-client/petanque";
import { GoalConfig } from "../lib/types";

/**
 * Type of the API exposed by the Waterproof extension.
 *
 * Extensions that rely on the Waterproof API contributed by the Waterproof extension
 * can copy this type and use it in: `extensions.getExtension<WaterproofAPI>("waterproof-tue.waterproof");`
 */
export type WaterproofAPI = {
    /**
     * Returns the goals at the position of the user cursor.
     * - `currentGoal`: String representation of the the current goal.
     * - `hypotheses`: Array of objects containing a name and content of the hypotheses.
     * - `otherGoals`: Other remaining goals in open proofs.
     */
    goals: () => Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}>;
    /**
     * Returns the `TextDocument` object of the open document in which the user cursor
     * is located.
     */
    currentDocument: () => TextDocument;
    /**
     * Executes the `Help.` command at the cursor position and returns the output as an array of strings.
     */
    help: () => Promise<Array<string>>;
    /**
     * Returns information about the current proof on a document level.
     * This function will look at the current document to figure out what
     * statement the user is currently proving.
     * @param cursorMarker The marker string to insert to indicate where the user has placed there
     * cursor in the current proof.
     * @returns An object containing:
     * - `name`: The name of the provable statement.
     * - `full`: The full statement that the user is working on from Theorem, Lemma, etc to Qed.
     * - `withCursorMarker`: The same as `full` but contains the {@linkcode cursorMarker} at the point where
     * the user has placed the cursor.
     */
    proofContext: (cursorMarker: string) => Promise<{ 
        name: string,
        full: string,
        withCursorMarker: string
    }>;
    /**
     * Executes a command at the cursor position and returns the full output including messages,
     * goals, goal stack, etc. See {@linkcode GoalConfig} and {@linkcode RunResult} for more details.
     */
    execCommand: (cmd: string) => Promise<GoalConfig<string> & RunResult<number>>;
    /**
     * Try a proof/step by executing the given commands/tactics.
     * @param steps The proof steps to try. This can be a single tactic or command or multiple separated by the
     * usual `.` and space.
     */
    tryProof: (steps: string) => Promise<{finished: boolean, remainingGoals: string[]}>;
    /**
     * Returns the cursor position known by the extension or `undefined` if there is none.
     */
    cursorPosition: () => Position | undefined;
}

/** The type of a hypothesis, a pair containing the name and the content */
export type Hypothesis = {
    name: string;
    content: string;
}
