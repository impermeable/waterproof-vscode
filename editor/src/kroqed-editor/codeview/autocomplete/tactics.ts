import { Completion, CompletionContext, CompletionSource, snippetCompletion } from "@codemirror/autocomplete";
import tactics from "./tactics.json";

const tacticCompletions: Completion[] = tactics.map((value) => {
    return snippetCompletion(value.template, value);
});

export const tacticCompletionSource: CompletionSource = function(context: CompletionContext) {
    let before = context.matchBefore(/\\+(\w+\-*)*/);
    // If completion wasn't explicitly started and there
    // is no word before the cursor, don't open completions.
    if (!context.explicit && !before) return null;
    return {
        from: before ? before.from : context.pos,
        options: tacticCompletions,
        validFor: /^\w*$/
    }
}