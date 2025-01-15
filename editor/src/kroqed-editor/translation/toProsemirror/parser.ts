/** The pretty-printing table. */
const ppTable: Map<string, string> = new Map();

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
    const listMatchesPlaceHolder = Array.from(commentInside.matchAll(/( {2})\-/g));
    listMatchesPlaceHolder.forEach((match) => {
        const orig = match[0];
        commentInside = commentInside.replace(orig, `....-`);
    });
    const listMatches = Array.from(commentInside.matchAll(/(\.{4})\-/g));
    listMatches.forEach((match) => {
        const orig = match[0];
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
    commentInside = commentInside.replaceAll(/\[([\s\S]+)\]/g, `\`$1\``);

    // Try to apply every pretty printing rule.
    ppTable.forEach((value: string, key: string) => {
        commentInside = commentInside.replaceAll(key, value);
    });

    return commentInside
}

export function toMathInline(from: "coqdoc" | "markdown", input: string): string {
    if (from === "coqdoc") {
        return input.replaceAll(/%(.*?)%/g, "<math-inline>$1</math-inline>");;
    } else if (from === "markdown") {
        return input.replaceAll(/\$(.*?)\$/g, "<math-inline>$1</math-inline>");
    } 
    throw new Error(`Unexpected type '${from}' in toMathInline`);
}