import { Completion, CompletionContext, CompletionResult, CompletionSource, snippetCompletion } from "@codemirror/autocomplete";
import tactics from "../../../../shared/completions/tactics.json";
import tacticsCoq from "../../../../shared/completions/tacticsCoq.json";

export function initializeTacticCompletion(useTacticsCoq: boolean = false) {
  TacticCompletion.initialize(useTacticsCoq); // Initialize the singleton instance
}

// Singleton method
class TacticCompletion {
  private tacticCompletions: Completion[] = [];
  private static instance: TacticCompletion | null = null;

  private constructor(useTacticsCoq: boolean) {
    this.initializeCompletions(useTacticsCoq);
  }

  private async initializeCompletions(useTacticsCoq: boolean) {
    if (useTacticsCoq) {
        this.tacticCompletions = tacticsCoq.map((value) => {
          return snippetCompletion(value.template, value);
        });
    } else {
        this.tacticCompletions = tactics.map((value) => {
          return snippetCompletion(value.template, value);
        });
    }
  }

  /* Public function to initialize based on selected setting */
  public static initialize(useTacticsCoq: boolean = false): void {
    this.instance = new TacticCompletion(useTacticsCoq);
  }

  /* Instance getter to pass instance to nodeview.ts */
  static getInstance(useTacticsCoq: boolean = false): TacticCompletion {
    if (!this.instance) {
      this.instance = new TacticCompletion(useTacticsCoq);
    }
    return this.instance;
  }


public tacticCompletionSource: CompletionSource = function(context: CompletionContext): Promise<CompletionResult | null> {
  return new Promise((resolve, reject) => {
      let Beforecontext = this.state.doc
      let before = context.matchBefore(/([^\s\.\n\t\-\+\*])[^\s\n\t\-\+\*]*/gm);
      let period = /\./gm //Regex expression to search entire line for period
      // Get the line containing the cursor position
      const line = context.state.doc.lineAt(context.pos);
      const firstletter = line.text.match(/[a-zA-Z]/);

      // Extract the text from the start of the line to the cursor position
      const lineBeforeCursor = line.text.slice(0, context.pos - line.from);
      
      if ((!context.explicit && !before) || period.test(lineBeforeCursor)) resolve(null);
      resolve({
        from: firstletter ? line.from + firstletter.index!: context.pos,
        // non-null assertion operator "!" used to remove 'possibly null' error
        options: TacticCompletion.instance!.tacticCompletions,
        validFor: /^[\t]*[^\.]*/gm
      })
  });
}
}

/*
public tacticCompletionSource: CompletionSource = function(context: CompletionContext): Promise<CompletionResult | null> {
  return new Promise((resolve, reject) => {
      //let before = context.matchBefore(/([^\s\.\n\t\-\+\*])[^\s\n\t\-\+\*]*//*gm);
      let completionRegex = /([^\s\.\n\t\-\+\*])[^\s\n\t\-\+\*]*//*gm
      let Tokenbefore = context.tokenBefore(['string']);

      // Check if Tokenbefore is null
      if (!Tokenbefore) {
        resolve(null); // No valid token before, no suggestions
        return;
    }

      let before = completionRegex.test(Tokenbefore.text);
      let period = /\./gm //Regex expression to search entire line for period

      if ((!context.explicit && !before) || period.test(Tokenbefore.text)) resolve(null);
      resolve({
        from: before ? Tokenbefore.from : context.pos,
        // non-null assertion operator "!" used to remove 'possibly null' error
        options: TacticCompletion.instance!.tacticCompletions,
        validFor: /^[\t]*[^\.]*//*gm
      })
  });
}
}*/


// Export the singleton instance to nodeview.ts
export const tacticCompletionSource = TacticCompletion.getInstance().tacticCompletionSource;
