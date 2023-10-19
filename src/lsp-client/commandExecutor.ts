import { Position, Range, WorkspaceEdit, workspace } from "vscode";
import { Position as LSPPosition } from "vscode-languageserver-types";
import { GoalAnswer, Message, PpString, convertToString } from "../../lib/types";
import { CoqLspClient } from "./clientTypes";

/**
 * Utility function used to edit the active document. Note that this increments the document's
 * version, which is desired since every variant processed by the LSP server must have a unique
 * version.
 */
async function edit(f: (e: WorkspaceEdit) => void): Promise<void> {
    const e = new WorkspaceEdit();
    f(e);
    await workspace.applyEdit(e);  // TODO: what does boolean result mean?
}

/**
 * Converts a goals response to a list of pretty-printed results.
 */
function getResults(response: GoalAnswer<PpString>): PpString[] {
    let messages = response.messages;

    // unbox `Message` if necessary s.t. `messages` is of type `PpString[]`
    if (messages.length && typeof messages[0] === "object" && "text" in messages[0]) {
        messages = (messages as Message<PpString>[]).map(m => m.text);
    }

    return messages as PpString[];
}

const lspPositionToPosition = (position: LSPPosition) => new Position(position.line, position.character);

export async function executeCommand(client: CoqLspClient, command: string): Promise<GoalAnswer<PpString>> {
    const documentUri = client.activeDocument?.uri;
    if (!documentUri) {
        throw new Error("Cannot execute command; there is no active document.");
    }

    const document = await client.getDocument();
    let commandPos = undefined;
    const activeCursorPosition = client.activeCursorPosition;
    if (!activeCursorPosition) throw new Error("Cannot execute command; there is no active cursor position");
    if (document.completed.status[0] === "Yes") {
        const filtered = document.spans.filter((span) => {
            const spanPos = new Position(span.range.end.line, span.range.end.character);
            return activeCursorPosition.isAfterOrEqual(spanPos);
        });
        const first = filtered[filtered.length - 1];
        commandPos = lspPositionToPosition(first.range.end);
    }

    // Fall back to old function in the case that the request document does not work.
    const useGetDocumentOne = (commandPos !== undefined);
    console.log(`useGetDocumentOne : ${useGetDocumentOne}`);
    const commandPosition = useGetDocumentOne ? commandPos : client.getEndOfCurrentSentence(); 

    if (!commandPosition) {
        throw new Error("Cannot execute command; the document contains no Coq code.");
    }

    // 1. upload (temporary) version of document that includes `command`
    await edit(e => {
        // note: Coq requires a space between a period and the next sentence
        e.insert(documentUri, commandPosition, ' ' + command);
    });

    // 2. request goals for `command`
    const response = await client.requestGoals(commandPosition.translate(0, 1));

    // 3. upload original document to "restore" it
    await edit(e => {
        const r = new Range(commandPosition, commandPosition.translate(0, 1 + command.length));
        e.delete(documentUri, r);
    });

    // 4. process messages and return results (temp)
    if (response.error)
        throw new Error(convertToString(response.error));
    else
        return response;
}
