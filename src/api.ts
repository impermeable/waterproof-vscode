import { TextDocument } from "vscode";

export type WaterproofAPI = {
    goals: () => Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}>;
    currentDocument: () => TextDocument;
    help: () => Promise<Array<string>>;
    proofContext: () => { lemma: string, soFar: string };
    tryProof: (steps: string) => Promise<{finished: boolean, remainingGoals: string[]}>; 
}

export type Hypothesis = {
    name: string;
    content: string;
}
