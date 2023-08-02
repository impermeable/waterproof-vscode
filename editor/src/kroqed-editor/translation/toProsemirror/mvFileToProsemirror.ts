import { parseAsMv } from "./parseAsMv";



/**
 * Should behave as follows.
 * 1:   match all coqblocks (```coq ... ```)
 * 1.1: run .v translator on blocks. 
 * 1.2: run .mv translator (using special metadata) on these blocks. 
 * 2:   run .mv translator on all other blocks.
 */

/** Enum storing the cell type, can either be coqdoc or coq code*/
enum coqCellType {
    CoqDoc, 
    CoqCode
}

enum CellType {
    Coq, 
    Text
}

interface CoqBlock {
    start: number; 
    end: number;
    content: string | RegExpMatchArray;
    type: CellType;
}

function getAllCoqBlocks(input: string): CoqBlock[] {
    // Regex to find all coq blocks
    const coqblockRegExp = /(\r\n|\n)?^```coq(\r\n|\n)([^]*?)(\r\n|\n)?^```$(\r\n|\n)?/gm;

    // Get all the matchings
    const matches: RegExpMatchArray[] = Array.from(input.matchAll(coqblockRegExp));

    // Loop through matches and replace newlines with a string to be used in html tags
    for (let i = 0; i < matches.length; i++) {
        for (let j = 0; j < matches[i].length; j++) {
            if (matches[i][j] == undefined) {
                matches[i][j] = ""
            } else if (matches[i][j] == "\r\n" || matches[i][j] == "\n") {
                matches[i][j] = "newLine"
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
            type: CellType.Coq
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
function extractText(document: string, cbs: CoqBlock[]): CoqBlock[] {
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
                type: CellType.Text,
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
            type: CellType.Text,
            content: substring
        });
    }

    return textBlocks;
}

export function translateMvToProsemirror(inputDocument: string): string {

    // Get all coq blocks using there tags (```coq and ```)
    const allCoqBlocks = getAllCoqBlocks(inputDocument);
    // Get all text blocks by looking at what is left
    const allTextBlocks = extractText(inputDocument, allCoqBlocks);

    let allBlocks = allCoqBlocks.concat(allTextBlocks);
    // sort the blocks on there start in the document (happens in place)
    allBlocks.sort((a, b) => {
        return a.start - b.start;
    });

    // allBlocks is now an ordered array of all blocks (Text and Code) 

    // Store the parsed document contents
    let parsedDocument = "";

    allBlocks.forEach(block => {
        if (block.type === CellType.Coq) {
            // Coqcode, run .v parser
            parsedDocument += handleCoqBlock(block.content as RegExpMatchArray);

        } else if (block.type === CellType.Text) {
            // This is a 'markdown' (normal text) block. 
            parsedDocument += handleTextBlock(block.content as string);
        }
    });
    return parsedDocument;
}


/**
 * Deal with a coq block. Translates as follows: coqblock -> .mv format -> prosemirror format.
 * @param match RegExpMatchArray of the matching coqblock. 
 * @returns parsed coq block 
 */
function handleCoqBlock(match: RegExpMatchArray) {
    let content = match[3];

    let allCoqDoc = getAllCoqdoc(content);
    let coqDoc: Array<coqFileEntry> = allCoqDoc.map((doc) => {
        let start = doc.index;
        if (start == undefined) {
            throw new Error("");
        }
        let end = start + doc[0].length;
        return {content: doc, start, end, type: coqCellType.CoqDoc};
    });
    
    let allCoqBlocks = getAllCoq(content, allCoqDoc);

    let allCells: Array<coqFileEntry> = [...allCoqBlocks, ...coqDoc];
    // Content is now basically its own little .mv file. 
    // We can run the .mv parser over this.

    // TODO: There may be a more elegant way to do this. We should not add them in the first place. 
    let markForRemoval: Array<number> = [];
    allCells.forEach((item, index) => {
        if (item.type == coqCellType.CoqCode && item.content === "") {
            markForRemoval.push(index);
        }
    });
    // We have to loop in reverse order here, otherwise removing
    //   elements messes up the index of the later ones.
    for (var i = markForRemoval.length - 1; i >= 0; i--) {
        allCells.splice(markForRemoval[i], 1);
    }

    // Sort the cells on there index.
    allCells = allCells.sort((item1, item2) => {
        return item1.start - item2.start;
    });

    // This makes sure we do not forget any trailing coq code.
    if (allCells.length > 0) {
        let endEnd = allCells[allCells.length - 1].end;
        if (endEnd < content.length) {
            let substring = content.substring(endEnd); // TODO: Same as above
            allCells.push({content: substring, start: endEnd, end: content.length, type: coqCellType.CoqCode})
        }
    }

    if (allCells.length == 0 && content.length > 0) {
        // The case where there is no coqdoc but coq
        allCells.push({content, start: 0, end: content.length, type: coqCellType.CoqCode});
    }

    let result = ""
    allCells.forEach(cell => {
        if (cell.type === coqCellType.CoqCode) {
            // Coqcode, run .v parser
            result += `<coqcode>`.concat(cell.content as string, `</coqcode>`);

        } else if (cell.type === coqCellType.CoqDoc) {
            // This is a 'markdown' (normal text) block. 
            result += `<coqdoc preWhite="`+ cell.content[1] + `" postWhite="` + cell.content[3] +`">`.concat(parseAsMv(cell.content[2] as string, "coqdown"),`</coqdoc>`);
        }
    });

    if (result === "") {
        result = `<coqblock prePreWhite="`+ match[1] +`" prePostWhite="`+ match[2] +`" postPreWhite="`+ match[4] +`" postPostWhite="`+ match[5] +`"><coqcode></coqcode><\/coqblock>`
    } else {
        result = `<coqblock prePreWhite="`+ match[1] +`" prePostWhite="`+ match[2] +`" postPreWhite="`+ match[4] +`" postPostWhite="`+ match[5] +`">` + result + `<\/coqblock>`
    }
    

    return result;
}

/**
 * Deal with a text block. 
 * @param content String containing the markdown of this textblock.
 * @returns parsed markdown.
 */
function handleTextBlock(content: string) {
    return parseAsMv(content, "markdown");
}

/**
 * Gets all coqdoc comments from the document.
 * @param content The input .v document string.
 * @returns Array of `RegExpMatchArray`'s containing all the coqdoc comments.
 */
function getAllCoqdoc(content: string): RegExpMatchArray[] {
    /** 
    * RegExp that matches coqdoc comments. 
    * Coqdoc comments should be of the form 
    * `(** comment text here*)`
    * https://coq.inria.fr/refman/using/tools/coqdoc.html#principles
    */
    const regex = /(\r\n|\n)?^\(\*\* ([^]*?)\*\)$(\r\n|\n)?/gm;
    let result = Array.from(content.matchAll(regex))
    for (let i = 0; i < result.length; i++) {
        for (let j = 0; j < result[i].length; j++) {
            if (result[i][j] == undefined) {
                result[i][j] = ""
            } else if (result[i][j] == "\r\n" || result[i][j] == "\n") {
                result[i][j] = "newLine"
            }
        }
    }
    return result;
}



/** Basic interface for a coq file entry.  */
interface coqFileEntry{
    content: string | RegExpMatchArray;
    start: number;
    end: number;
    type: coqCellType;
}

/**
 * Retrieves all coq code blocks from the document.
 * @param content The document content
 * @param matches Array of matches for coqdoc strings
 * @returns All coq code blocks
 */
function getAllCoq(content: string, matches: RegExpMatchArray[]) {
    let coqBlocks = new Array<coqFileEntry>();
    let prevEnd = 0;
    matches.forEach((match) => {
        let start = match.index;
        if (start == undefined) {
            throw new Error("Start is undefined");
        }
        let end = start + match[0].length;
        if (prevEnd != start) {
            let substring = content.substring(prevEnd, start);
            coqBlocks.push({content: substring, start: prevEnd, end: start, type: coqCellType.CoqCode});
        }
        prevEnd = end;
    });
    return coqBlocks;
}