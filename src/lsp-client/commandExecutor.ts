import { Position } from "vscode";
import { GoalAnswer, GoalConfig } from "../../lib/types";
import { CoqLspClient } from "./clientTypes";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { GetStateAtPosParams, getStateAtPosReq, GoalsParams, goalsReq, Run_result, RunParams, runReq } from "./petanque";

async function executeCommandBase(client: CoqLspClient, command: string) {
    const document = client.activeDocument;

    if (!document) {
        throw new Error("Cannot execute command; there is no active document.");
    }

    // We execute the command at the end of the previous sentence.
    const commandPosition = client.getBeginningOfCurrentSentence();
    if (!commandPosition) {
        throw new Error("Cannot execute command; the document contains no Coq code.");
    }

    const pos = { offset: document.offsetAt(commandPosition) - 1, line: commandPosition.line, character: commandPosition.character - 1 };
    const params: GetStateAtPosParams = {
        // Make sure that the position is **before** the dot, otherwise there is no node at the position.
        position: pos,
        uri: document.uri.toString()
    }

    try {
        const stateRes = await client.sendRequest(getStateAtPosReq, params);
        // Create the RunParams object, st is the state to execute in, tac the command
        // to execute.
        const runParams: RunParams = { st: stateRes.st, tac: command };
        const runRes = await client.sendRequest(runReq, runParams);
        // The state on which to query the goals is the state *after* the command has been run.
        const goalParams: GoalsParams = { st: runRes.st };
        const goalsRes = await client.sendRequest(goalsReq, goalParams);

        return {
            goalsRes, runRes, document
        };
    } catch (error) {
        throw new Error(`Error when trying to execute command '${command}': ${error}`);
    }
}

export async function executeCommand(client: CoqLspClient, command: string): Promise<GoalAnswer<string>> {
    try {
        const { goalsRes, runRes, document } = await executeCommandBase(client, command);
        return {
            messages: runRes.feedback.map((val) => { return { level: val[0], text: val[1] } }),
            position: new Position(0, 0),
            textDocument: VersionedTextDocumentIdentifier.create(document.uri.toString(), document.version),
            goals: goalsRes
        };
    } catch (error) {
        throw new Error(`Error when trying to execute command '${command}': ${error}`);
    }
}

export async function executeCommandFullOutput(client: CoqLspClient, command: string): Promise<GoalConfig<string> & Run_result<number>> {
    try {
        const { goalsRes, runRes } = await executeCommandBase(client, command);
        return { ...goalsRes, ...runRes };
    } catch (error) {
        throw new Error(`Error when trying to execute command '${command}': ${error}`);
    }
}