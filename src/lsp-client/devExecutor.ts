import { Position, Range, WorkspaceEdit, workspace } from "vscode";
import { Position as LSPPosition, VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { GoalAnswer, Message, PpString, convertToString, GoalRequest } from "../../lib/types";
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

export async function executeTestCommand(client: CoqLspClient, command: string): Promise<GoalAnswer<PpString>> {
    const documentUri = client.activeDocument?.uri;
    const version = client.activeDocument?.version as number;
    if (!documentUri) {
        throw new Error("Cannot execute command; there is no active document.");
    }

    // We execute the command at the end of the previous sentence.
    const commandPosition = client.getBeginningOfCurrentSentence();
    if (!commandPosition) {
        throw new Error("Cannot execute command; the document contains no Coq code.");
    }

    // 2. request goals for `command`
    let params: GoalRequest = {
        textDocument: VersionedTextDocumentIdentifier.create(documentUri.toString(), version),
        position: commandPosition.translate(0,1),
        pretac: "Help."
        // pretac: "Expand the definition of is_lub in is_sup [0,1] 1."
    };
    const response = await client.requestGoals(params);

    // let messages = response.messages;
    // // unbox `Message` if necessary s.t. `messages` is of type `PpString[]`
    // if (messages.length && typeof messages[0] === "object" && "text" in messages[0]) {
    //     messages = (messages as Message<PpString>[]).map(m => m.text);
    // }
    // console.log(messages);
    

    // 4. process messages and return results (temp)
    if (response.error)
        throw new Error(convertToString(response.error));
    else
        return response;
}
