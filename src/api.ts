import { Position, TextDocument } from "vscode";
import { RunResult } from "./lsp-client/petanque";
import { GoalConfig } from "../lib/types";

export type WaterproofAPI = {
    /**
     * Returns an object containg the goal of the current proof together with its hyptheses.
     * Also contains other possibly open goals.
     */
    goals: () => Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}>;
    /**
     * Retrieve the current document the user is working on.
     */
    currentDocument: () => TextDocument;
    /**
     * Executes the `Help.` command at the cursor position and returns string representations
     * of the messages returned.
     */
    help: () => Promise<Array<string>>;
    /**
     * Returns context about the current proof the user is working on. This includes the name of the statement
     * and the whole proof with and without a marker indicating the position of the user cursor.
     */
    proofContext: (cursorMarker: string) => Promise<{ 
        name: string,
        full: string,
        withCursorMarker: string
    }>;
    /**
     * Execute the command in `cmd` and returns all the output we get from Petanque.
     * See {@linkcode GoalConfig} and {@linkcode RunResult} for more details.
     */
    execCommand: (cmd: string) => Promise<GoalConfig<string> & RunResult<number>>;
    /** Try the steps in `steps` (there can be more than one, separated by `.`).
      * The result will be an object containing
      * - `finished: boolean`: Indicating whether this step finsihed the current proof.
      * - `remainingGoals: string[]`: String representations of all remaining goals after executing `steps`. 
      */
    tryProof: (steps: string) => Promise<{finished: boolean, remainingGoals: string[]}>;
    /** Retrieve the cursor position in the current active document (returns `undefined` if there is none) */
    cursorPosition: () => Position | undefined;
}

export type Hypothesis = {
    name: string;
    content: string;
}
