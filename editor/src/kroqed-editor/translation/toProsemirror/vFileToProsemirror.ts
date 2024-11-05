
/** Enum storing the cell type, can either be coqdoc or coq code*/

enum CellType {
    Code, 
    Coqdoc
}

interface CoqBlock {
    start: number; 
    end: number;
    content: string | RegExpMatchArray;
    type: CellType;
}


export function translateVToProsemirror(inputDocument: string): string {

    // Input areas
    // Regex to find all coq blocks
    const regex = /(\r\n|\n)?\(\* begin input \*\)(\r\n|\n)?([^]*?)(\r\n|\n)?\(\* end input \*\)(\r\n|\n)?/gm;

    // Get all the matchings
    const matches: RegExpMatchArray[] = Array.from(inputDocument.matchAll(regex));

    // Loop through matches and replace newlines with a string to be used in html tags
    for (let i = 0; i < matches.length; i++) {
        for (let j = 0; j < matches[i].length; j++) {
            if (j != 0 && j != 3) {
                if (matches[i][j] == undefined) {
                    matches[i][j] = ""
                } else if (matches[i][j] == "\r\n" || matches[i][j] == "\n") {
                    matches[i][j] = "newLine"
                }
            }     
        }
    }

    matches.forEach(match => {
        inputDocument = inputDocument.replace(/(\r\n|\n)?\(\* begin input \*\)(\r\n|\n)?([^]*?)(\r\n|\n)?\(\* end input \*\)(\r\n|\n)?/gm, `\<input-area prePreWhite="${match[1]}" prePostWhite="${match[2]}" postPreWhite="${match[4]}" postPostWhite="${match[5]}"\>$3<\/input-area>`)
    });

    // For hints
    const hintRegEx = /\(\* begin hint : ([^"]+?) \*\)/gm;
    inputDocument = inputDocument.replaceAll(hintRegEx, `<hint title=$1>`);

    const endhintRegEx = /\(\* end hint \*\)/gm;
    inputDocument = inputDocument.replaceAll(endhintRegEx, `<\/hint>`);

    const regex2 = /(\r\n|\n)?<hint title=([^"]+?)>(\r\n|\n)?([^]*?)(\r\n|\n)?<\/hint>(\r\n|\n)?/gm;

    // Get all the matchings
    const matches2: RegExpMatchArray[] = Array.from(inputDocument.matchAll(regex2));



    // Loop through matches and replace newlines with a string to be used in html tags
    for (let i = 0; i < matches2.length; i++) {
        for (let j = 0; j < matches2[i].length; j++) {
            if (j != 0 && j != 2 && j != 4) {
                if (matches2[i][j] == undefined) {
                    matches2[i][j] = ""
                } else if (matches2[i][j] == "\r\n" || matches2[i][j] == "\n") {
                    matches2[i][j] = "newLine"
                }
            }     
        }
    }

    
    matches2.forEach(match => {
        inputDocument = inputDocument.replace(/(\r\n|\n)?<hint title=([^"]+?)>(\r\n|\n)?([^]*?)(\r\n|\n)?<\/hint>(\r\n|\n)?/gm, `\<hint title=${match[2]} prePreWhite="${match[1]}" prePostWhite="${match[3]}" postPreWhite="${match[5]}" postPostWhite="${match[6]}"\>$4<\/hint>`)
    });



    // Get all coq blocks using there tags (```coq and ```)
    const allCoqDocBlocks = getAllCoqDocBlocks(inputDocument);
    // Get all text blocks by looking at what is left
    const allCodeBlocks = extractCode(inputDocument, allCoqDocBlocks);

    let allBlocks = allCoqDocBlocks.concat(allCodeBlocks);
    // sort the blocks on there start in the document (happens in place)
    allBlocks.sort((a, b) => {
        return a.start - b.start;
    });

    // allBlocks is now an ordered array of all blocks (Text and Code) 

    // Store the parsed document contents
    let parsedDocument = "";

    allBlocks.forEach(block => {
        if (block.type === CellType.Coqdoc) {
            // Coqcode, run .v parser
            parsedDocument += handleCoqDocBlock(block.content as RegExpMatchArray);

        } else if (block.type === CellType.Code) {
            // This is a 'markdown' (normal text) block. 
            parsedDocument += handleCodeBlock(block.content as string);
        }
    });

    //Remove all empty markdown blocks (so only those with absolutely no text)
    const removeRegEx = new RegExp(`<coqblock prePreWhite="" prePostWhite="" postPreWhite="" postPostWhite="">()<\/coqblock>`, "gm")
    parsedDocument = parsedDocument.replaceAll(removeRegEx, ""); 
    //Remove all empty markdown blocks (so only those with absolutely no text)
    const removeRegEx1 = new RegExp(`<\/coqblock>()<coqblock prePreWhite="" prePostWhite="" postPreWhite="" postPostWhite="">`, "gm")
    parsedDocument = parsedDocument.replaceAll(removeRegEx1, ""); 
    console.log(parsedDocument)
    return parsedDocument;
}

function getAllCoqDocBlocks(input: string): CoqBlock[] {
    // Regex to find all coq blocks
    const regex = /(\r\n|\n)?\(\*\* ([^]*?)\*\)(\r\n|\n)?/gm;

    // Get all the matchings
    const matches: RegExpMatchArray[] = Array.from(input.matchAll(regex));

    // Loop through matches and replace newlines with a string to be used in html tags
    for (let i = 0; i < matches.length; i++) {
        for (let j = 0; j < matches[i].length; j++) {
            if (j != 0 && j != 2) {
                if (matches[i][j] == undefined) {
                    matches[i][j] = ""
                } else if (matches[i][j] == "\r\n" || matches[i][j] == "\n") {
                    matches[i][j] = "newLine"
                }
            }     
        }
    }

    // Create array for coqblock saving
    let coqBlocks: CoqBlock[] = [];

    // Loop through coqblocks and add them to the array appropiately
    matches.forEach(match => {
        // Compute information about position of the coqblocks
        let length = match[0].length;
        let start = match.index;
        if (start === undefined) {
            throw new Error("Index cannot be null");
        }
        let end = start + length;

        // Add the coqblock with the information to the array
        coqBlocks.push({
            start, 
            end, 
            content: match, 
            type: CellType.Coqdoc
        });
    });
    return coqBlocks;
}

/**
 * Extracts text from document based on an array of extracted coqblocks. Takes
 * out all the text inbetween the coqblocks and at the start or end of the document.
 * 
 * @param document the document in question
 * @param cbs the array of coqblocks
 * @returns an array of textblocks with type Text
 */
function extractCode(document: string, cbs: CoqBlock[]): CoqBlock[] {
    // Initialize array to save text blocks
    let textBlocks: CoqBlock[] = [];
    let prevEnd = 0;

    // loop through all coqblocks and push the text between the coqblocks
    cbs.forEach(cb => {
        if (cb.start != prevEnd) {
            const substring = document.substring(prevEnd, cb.start);

            // Push a new text block
            textBlocks.push({
                start: prevEnd, 
                end: cb.start, 
                type: CellType.Code,
                content: substring
            });
        }

        prevEnd = cb.end;
    });

    // Add final cell after the last coq block if it exists
    if (prevEnd != document.length) {
        const substring = document.substring(prevEnd, document.length);

        // Push the cell
        textBlocks.push({
            start: prevEnd, 
            end: document.length, 
            type: CellType.Code,
            content: substring
        });
    }

    return textBlocks;
}

/**
 * Deal with a coq block. Translates as follows: coqblock -> .mv format -> prosemirror format.
 * @param match RegExpMatchArray of the matching coqblock. 
 * @returns parsed coq block 
 */
function handleCoqDocBlock(match: RegExpMatchArray) {

    // TODO: ADD COQDOC PARSING
    if (match[2] != "") {
        let input = match[2]

        let markDownType = "coqdown"

        let match1 = match[1]

        if (match1 == undefined) {
            match1 = ""
        }

        let match3 = match[3]

        if (match3 == undefined) {
            match3 = ""
        }

        input = `<coqblock prePreWhite="" prePostWhite="" postPreWhite="" postPostWhite=""><coqdoc prePreWhite="`+ match1 +`" prePostWhite="" postPreWhite="" postPostWhite="`+ match3 +`"><coqdown>`.concat(input)



        // This is for markdown replacement with text
        const mathdisplayRegEx = /(?<!(?:\\|\`))(?:((?<!\$)\${1}(?!\$)))([^]*?)(?<!(?:\\|\`))(?<!\$)\1(?!\$)/gm
        input = input.replaceAll(mathdisplayRegEx, `<\/${markDownType}><math-display>$2</math-display><${markDownType}>`)

        // This is for empty cells
        const mathdisplayRegEx2 = /(?<!(?:\\|\`))\${2}/gm
        input = input.replaceAll(mathdisplayRegEx2, `<\/${markDownType}><math-display></math-display><${markDownType}>`)

        //Closing markdown
        input = input.concat(`<\/coqdown><\/coqdoc><\/coqblock>`)

        const removeRegEx2 = new RegExp(`<coqdown><\/coqdown>`, "gm")
        input = input.replaceAll(removeRegEx2, ""); 



        return input;
    } else {
        throw new Error("Empty comment inserted which should not be possible")
    }
}


/**
 * Deal with a text block. 
 * @param content String containing the markdown of this textblock.
 * @returns parsed markdown.
 */
function handleCodeBlock(content: string) {
    return parseAsV(content);
}

/**
 * Parses `content` as .mv file content. 
 * @param content The content that should be parsed.
 * @returns The parsed content.
 */
function parseAsV(input: string) {

    let preString = `<coqblock prePreWhite="" prePostWhite="" postPreWhite="" postPostWhite=""><coqcode>`

    let postString = `<\/coqcode><\/coqblock>`
    
    // Add pre-markdown tag
    input = preString.concat(input)
    // Math-display replacement for markdown

    // Input areas
    const inputAreaRegEx = /(<input-area ([^]*?)?>)/gm
    input = input.replaceAll(inputAreaRegEx, `${postString}$1${preString}`)

    const endinputAreaRegEx = /(<\/input-area>)/gm
    input = input.replaceAll(endinputAreaRegEx, `${postString}$1${preString}`)

    // For hints
    const hintRegEx = /<hint ([^]*?)?>/gm;
    input = input.replaceAll(hintRegEx, `${postString}<hint $1>${preString}`);

    const endhintRegEx = /<\/hint>/gm;
    input = input.replaceAll(endhintRegEx, `${postString}<\/hint>${preString}`);

    //Closing markdown
    input = input.concat(`${postString}`)

    //Remove all empty markdown blocks (so only those with absolutely no text)
    const removeRegEx = new RegExp(`<\/coqblock>()<coqblock prePreWhite="" prePostWhite="" postPreWhite="" postPostWhite="">`, "gm")
    input = input.replaceAll(removeRegEx, ""); 

    const removeRegEx2 = new RegExp(`<coqcode>()<\/coqcode>`, "gm")
    input = input.replaceAll(removeRegEx2, ""); 

    
    return input;
}

