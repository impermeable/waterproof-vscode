import { Completion, CompletionContext, CompletionResult, CompletionSource, snippetCompletion } from "@codemirror/autocomplete";
import tactics from "../../../../shared/completions/tactics.json";

const tacticCompletions: Completion[] = tactics.map((value) => {
    return snippetCompletion(value.template, value);
});

export const tacticCompletionSource: CompletionSource = function(context: CompletionContext): Promise<CompletionResult | null> {
    return new Promise((resolve, reject) => {
        let before = context.matchBefore(/(?<=^[ \t\-\+\*]*)([^ \t\-\+\*]*)/gm);
        if (!context.explicit && !before) resolve(null);
        resolve({
            from: before ? before.from : context.pos,
            options: tacticCompletions,
            validFor: /^[ \t]*[^\.]*/gm
        })
    });
}