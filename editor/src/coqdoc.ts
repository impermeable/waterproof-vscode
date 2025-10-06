/** The pretty-printing table. */
const ppTable: Map<string, string> = new Map();

/** 
 * Populate the pretty printing table according to: 
 * https://coq.inria.fr/refman/using/tools/coqdoc.html#pretty-printing  
 */
function populatePPTable() {
    ppTable.set("<->",  "↔");
    ppTable.set("->",   "→");
    ppTable.set("<-",   "←");
    ppTable.set("<=",   "≤");
    ppTable.set(">=",   "≥");
    ppTable.set("=>",   "⇒");
    ppTable.set("<>",   "≠");
    ppTable.set("\\/",  "∨");
    ppTable.set("/\\",  "∧");
    ppTable.set("|-",   "⊢");
    ppTable.set("~",    "¬");
}

export function translateCoqDoc(coqdoc: string) {
    populatePPTable();

    let commentInside = coqdoc;

    /**
     * Replace headers according to
     * https://coq.inria.fr/refman/using/tools/coqdoc.html#sections
     * 
     * The order here matters so go from more * to less. 
     */
    // Replace all H4 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/^\*{4}\s+([^\n\r]+)/gm, "#### $1");
    // Replace all H3 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/^\*{3}\s+([^\n\r]+)/gm, "### $1");
    // Replace all H2 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/^\*{2}\s+([^\n\r]+)/gm, "## $1");
    // Replace all H1 headers inside the coqdoc comment with markdown header.
    commentInside = commentInside.replaceAll(/^\*{1}\s+([^\n\r]+)/gm, "# $1");

    // List (-)
    const listMatchesPlaceHolder = Array.from(commentInside.matchAll(/( {2})-/g));
    listMatchesPlaceHolder.forEach((match) => {
        const orig = match[0];
        commentInside = commentInside.replace(orig, `....-`);
    });
    const listMatches = Array.from(commentInside.matchAll(/(\.{4})-/g));
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
    commentInside = replaceCode(commentInside);

    // Try to apply every pretty printing rule.
    ppTable.forEach((value: string, key: string) => {
        commentInside = commentInside.replaceAll(key, value);
    });

    return commentInside
}

function replaceCode(input: string): string {
    let result = '';
    let depth = 0;

    for (const char of input) {
        if (char === '[') {
            if (depth === 0) {
                result += "`";
            } else {
                result += char;
            }
            // Opening bracket, increase depth.
            depth++;
        } else if (char === ']') {
            // Closing bracket, decrease depth.
            depth--;
            if (depth === 0) {
                result += "`";
            } else {
                result += char;
            }
        } else {
            result += char;
        }
    }

    if (depth !== 0) {
        // Unbalanced brackets in string, returning input
        return input;
    }

    return result;
}

function toMathInline(input: string): string {
    return input.replaceAll(/%(.*?)%/g, "<math-inline>$1</math-inline>");
}

export function coqdocToMarkdown(coqdoc: string): string {
    return toMathInline(translateCoqDoc(coqdoc));
}