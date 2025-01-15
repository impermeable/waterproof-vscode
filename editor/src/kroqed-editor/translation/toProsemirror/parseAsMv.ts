/**
 * Parses `content` as .mv file content. 
 * @param content The content that should be parsed.
 * @returns The parsed content.
 */
export function parseAsMv(input: string, markDownType: string) {
    
    // Add pre-markdown tag
    input = `<${markDownType}>`.concat(input)
    // Math-display replacement for markdown
    if (markDownType === "markdown") {

        // This is for markdown replacement with text
        const mathdisplayRegEx = /(?<!(?:\\|`))(?:((?<!\$)\${2}(?!\$)))([^]*?)(?<!(?:\\|`))(?<!\$)\1(?!\$)/gm
        input = input.replaceAll(mathdisplayRegEx, `</${markDownType}><math-display>$2</math-display><${markDownType}>`)

        // This is for empty cells
        const mathdisplayRegEx2 = /(?<!(?:\\|`))\${4}/gm
        input = input.replaceAll(mathdisplayRegEx2, `</${markDownType}><math-display></math-display><${markDownType}>`)
    
    // Math-display replacement for coqdown
    } else if (markDownType === "coqdown") {

        // This is for markdown replacement with text
        const mathdisplayRegEx = /(?<!(?:\\|`))(?:((?<!\$)\${1}(?!\$)))([^]*?)(?<!(?:\\|`))(?<!\$)\1(?!\$)/gm
        input = input.replaceAll(mathdisplayRegEx, `</${markDownType}><math-display>$2</math-display><${markDownType}>`)

        // This is for empty cells
        const mathdisplayRegEx2 = /(?<!(?:\\|`))\${2}/gm
        input = input.replaceAll(mathdisplayRegEx2, `</${markDownType}><math-display></math-display><${markDownType}>`)
    }
    
    // Input areas
    const inputAreaRegEx = /(<\/*?input-area>)/gm
    input = input.replaceAll(inputAreaRegEx, `</${markDownType}>$1<${markDownType}>`)

    // For hints
    const hintRegEx = /(<\/*?hint( \w+?="[^"]+?")*?>)/gm;
    input = input.replaceAll(hintRegEx, `</${markDownType}>$1<${markDownType}>`);

    //Closing markdown
    input = input.concat(`</${markDownType}>`)

    //Remove all empty markdown blocks (so only those with absolutely no text)
    const removeRegEx = new RegExp(`<${markDownType}>()</${markDownType}>`, "gm")
    input = input.replaceAll(removeRegEx, "");  
    
    return input;
}

