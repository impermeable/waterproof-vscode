import { Range, TextDocument } from "vscode";

import { GoalAnswer, PpString } from "../../lib/types";
import { ICoqLspClient } from "./clientTypes";
import { InputAreaStatus } from "waterproof-editor";

// TODO: only consider Markdown parts
function findOccurrences(substr: string, str: string): number[] {
    const indices: number[] = [];
    const substrLen = substr.length;
    for (let i = 0; (i = str.indexOf(substr, i)) >= 0; i += substrLen) indices.push(i);
    return indices;  // sorted
}

/** Returns whether input areas are not interleaved. */
function isValid(open: number[], close: number[]): boolean {
    if (open.length !== close.length) return false;
    if (open.length && open[0] > close[0]) return false;  // "base" case of loop below
    for (let i = 1; i < open.length; i++)
        if (close[i-1] > open[i] || open[i] > close[i])
            return false;
    return true;
}

export function getInputAreas(document: TextDocument): Range[] | undefined {
    const content = document.getText();

    // find (positions of) opening and closings tags for input areas, and check that they're valid
    const openOffsets = findOccurrences("<input-area>", content);
    const closeOffsets = findOccurrences("</input-area>", content);
    if (!isValid(openOffsets, closeOffsets)) return undefined;

    // map offsets to ranges
    const inputAreas: Range[] = [];
    for (let i = 0; i < openOffsets.length; i++) {
        inputAreas.push(new Range(
            document.positionAt(openOffsets[i]),
            document.positionAt(closeOffsets[i]),
        ));
    }
    return inputAreas;
}

function isComplete(response: GoalAnswer<PpString>): boolean {
    return !("error" in response);
}

export async function determineProofStatus(client: ICoqLspClient, document: TextDocument, inputArea: Range): Promise<InputAreaStatus> {
    // get the (end) position of the last line in the input area
    // funnily, it can be in a next input area, and we accept this
    const position = client.sentenceManager.getEndOfSentence(inputArea.end, true);
    if (!position) {
        // console.warn("qedStatus.ts : No sentence after input area");
        return InputAreaStatus.Invalid;
    }

    // check that last command is "Qed" (or return "invalid")
    // note that we don't allow, e.g., comments between "Qed" and "."
    const i = position.character - 4;
    if (i < 0 || document.lineAt(position).text.slice(i, i+4) !== "Qed.") {
        // console.warn("qedStatus.ts : Last sentence is not `Qed.`");
        return InputAreaStatus.Invalid;
    }

    // request goals and return conclusion based on them
    const response = await client.requestGoals(position.translate(0, -1));
    return isComplete(response) ? InputAreaStatus.Proven : InputAreaStatus.Incomplete;
}
