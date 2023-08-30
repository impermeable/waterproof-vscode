import { Completion, CompletionContext, CompletionResult, CompletionSource } from "@codemirror/autocomplete";
import symbols from "./symbols.json";

// Completions for common mathematical symbols.
const symbolCompletions: Completion[] = symbols;

/**
 * Function that creates the `symbolCompletionSource`. 
 * This function can be used in the editor as a completion source.
 */
export const symbolCompletionSource: CompletionSource = (context: CompletionContext): Promise<CompletionResult | null> => {
    return new Promise((resolve, reject) => {
        let before = context.matchBefore(/\\+(\w+\-*)*/);
        // If completion wasn't explicitly started and there
        // is no word before the cursor, don't open completions.
        if (!context.explicit && !before) resolve(null);
        resolve({
            from: before ? before.from : context.pos,
            options: symbolCompletions,
            validFor: /^\\*$/
        });
    });
    
}