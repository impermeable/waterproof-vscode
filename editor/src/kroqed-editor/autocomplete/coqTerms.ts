import { Completion, CompletionContext, CompletionResult, CompletionSource } from "@codemirror/autocomplete";
import coqWords from "./coqTerms.json";

// Our list of completions (can be static, since the editor
/// will do filtering based on context).
const coqCompletions: Completion[] = coqWords;

export const coqCompletionSource: CompletionSource = function(context: CompletionContext): Promise<CompletionResult | null> {
    return new Promise((resolve, _reject) => {
        const before = context.matchBefore(/\w/);
        const period = /\./gm //Regex expression to search entire line for period
        const contextline = context.state.doc.lineAt(context.pos).text // line at the completetion context
        // If completion wasn't explicitly started and there
        // is no word before the cursor, don't open completions.
        if ((!context.explicit && !before) || period.test(contextline)) resolve(null);
        resolve({
            from: before ? before.from : context.pos,
            options: coqCompletions,
            validFor: /[^ ]*/
        });
    });
}