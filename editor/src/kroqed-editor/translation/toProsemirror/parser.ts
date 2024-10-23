/** The pretty-printing table. */
let ppTable: Map<string, string> = new Map();

/** 
 * Populate the pretty printing table according to: 
 * https://coq.inria.fr/refman/using/tools/coqdoc.html#pretty-printing  
 */
function populatePPTable() {
    ppTable.set("->",   "→");
    ppTable.set("<-",   "←");
    ppTable.set("<=",   "≤");
    ppTable.set(">=",   "≥");
    ppTable.set("=>",   "⇒");
    ppTable.set("<>",   "≠");
    ppTable.set("<->",  "↔");
    ppTable.set("\\/",  "∨");
    ppTable.set("/\\",  "∧");
    ppTable.set("|-",   "⊢");
    ppTable.set("~",    "¬");
}

export function translateCoqDoc(entry: string) {
    populatePPTable();

    let commentInside = entry;

    /**
     * Replace headers according to
     * https://coq.inria.fr/refman/using/tools/coqdoc.html#sections
     * 
     * 
     * I hate this. The order here matters so go from more * to less. 
     */
    // Replace all H4 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/(?<![.A-Za-z\d(]+)\*{4}\s+([^\n\r]+)/g, "#### $1");
    // Replace all H3 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/(?<![.A-Za-z\d(]+)\*{3}\s+([^\n\r]+)/g, "### $1");
    // Replace all H2 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/(?<![.A-Za-z\d(]+)\*{2}\s+([^\n\r]+)/g, "## $1");
    // Replace all H1 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/(?<![.A-Za-z\d(]+)\*{1}\s+([^\n\r]+)/g, "# $1");

    // List (-)
    let listMatchesPlaceHolder = Array.from(commentInside.matchAll(/( {2})\-/g));
    listMatchesPlaceHolder.forEach((match) => {
        let orig = match[0];
        commentInside = commentInside.replace(orig, `....-`);
    });
    let listMatches = Array.from(commentInside.matchAll(/(\.{4})\-/g));
    listMatches.forEach((match) => {
        let orig = match[0];
        commentInside = commentInside.replace(orig, `    -`);
    });

    /** 
     * Replace verbatim input according to:
     * https://coq.inria.fr/refman/using/tools/coqdoc.html#verbatim
     */
    commentInside = commentInside.replaceAll(/<<\s*?\n([\s\S]+?)\n>>\s*?/g, `\`\`\`\n$1\n\`\`\``);
    
    /**
     * Replace "Preformatted vernacular" according to:
     * https://coq.inria.fr/doc/v8.12/refman/using/tools/coqdoc.html#coq-material-inside-documentation
     */
    commentInside = commentInside.replaceAll(/\[{2}\n([^]+)\n\]{2}/g, `\`\`\`\n$1\n\`\`\``);
    
    /** 
     * Replace quoted coq according to: 
     * https://coq.inria.fr/refman/using/tools/coqdoc.html#coq-material-inside-documentation
     */
    commentInside = replaceQuotedCoq(commentInside);

    // Try to apply every pretty printing rule.
    ppTable.forEach((value: string, key: string) => {
        commentInside = commentInside.replaceAll(key, value);
    });

    return commentInside
}

/**
 * Function to replace quoted coq in coqdoc comments with a markdown equivalent, i.e. replace [...] with `...`.
 * We use a custom stack-based approach here since regular expressions are not powerful enough to handle the nested brackets.
 * @param input The input string in which to replace the quoted coq.
 * @returns A new string with the quoted coq replaced.
 */
function replaceQuotedCoq(input: string): string {
    let result: string = input;
    let depth: number = 0;
    let quoteContent: string = '';
    let inQuote: boolean = false;

    for (const char of input) {
        if (char === '[') {
            if (inQuote) {
                // If we are already in a quote we increment the depth.
                depth++;
                // In this case add the char to the current quote.
                quoteContent += char;
            } else {
                // This indicates the beginning of a new quote.
                inQuote = true;
                depth++;
            }
        } else if (char === ']' && depth > 0) {
            // Closing square bracket has the potential to close this quote.
            depth--;
            if (depth == 0) {
                // If depth reaches 0, we have completed the topmost quote
                result = result.replace(`[${quoteContent}]`, `\`${quoteContent}\``);
                // We reset the current quote and flag.
                quoteContent = ''; 
                inQuote = false; 
            } else {
                quoteContent += char;
            }
        } else if (inQuote) {
            quoteContent += char;
        }
    }
    return result;
}

export function toMathInline(from: "coqdoc" | "markdown", input: string): string {
    if (from === "coqdoc") {
        return input.replaceAll(/%(.*?)%/g, "<math-inline>$1</math-inline>");;
    } else if (from === "markdown") {
        return input.replaceAll(/\$(.*?)\$/g, "<math-inline>$1</math-inline>");
    } 
    throw new Error(`Unexpected type '${from}' in toMathInline`);
}
