import { TextDocument } from "vscode";
import { RunResult } from "./lsp-client/petanque";
import { GoalConfig } from "../lib/types";

export type WaterproofAPI = {
    goals: () => Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}>;
    currentDocument: () => TextDocument;
    help: () => Promise<Array<string>>;
    proofContext: (cursorMarker: string) => Promise<{ 
        name: string,
        full: string,
        withCursorMarker: string
    }>;
    execCommand: (cmd: string) => Promise<GoalConfig<string> & RunResult<number>>;
    tryProof: (steps: string) => Promise<{finished: boolean, remainingGoals: string[]}>; 
}

export type Hypothesis = {
    name: string;
    content: string;
}
