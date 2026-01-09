import { Position } from "vscode";
import { CoqGoalAnswer, GoalConfig } from "../../lib/types";
import { LspClient } from "./abstractLspClient";
import { VersionedTextDocumentIdentifier } from "vscode-languageserver-types";
import { GetStateAtPosParams, getStateAtPosReq, GoalParams, goalsReq, RunParams, runReq, RunResult } from "./petanque";
import { CoqLspClient } from "./coqClient";

/**
 * Base function for executing tactics/commands in a client.
 */
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

    const pos = { line: commandPosition.line, character: commandPosition.character - 1 };
    const params: GetStateAtPosParams = {
        // Make sure that the position is **before** the dot, otherwise there is no node at the position.
        position: pos,
        uri: document.uri.toString()
    }

    try {
        const stateRes = await client.client.sendRequest(getStateAtPosReq, params);
        // Create the RunParams object, st is the state to execute in, tac the command
        // to execute.
        const runParams: RunParams = { st: stateRes.st, tac: command };
        const runRes = await client.client.sendRequest(runReq, runParams);
        // The state on which to query the goals is the state *after* the command has been run.
        const goalParams: GoalParams = { st: runRes.st };
        const goalsRes = await client.client.sendRequest(goalsReq, goalParams);

        return {
            goalsRes, runRes, document
        };
    } catch (error) {
        throw new Error(`Error when trying to execute command '${command}': ${error}`);
    }
}

/**
 * Execute `command` using client `client` and return the output formatted as a valid `GoalAnswer<string>`.
 * @param client The client to use when executing the command.
 * @param command The command/tactic to execute. It is allowed to execute multiple tactics/commands by seperating them using `.`'s.
 * @returns The output of executing `command` formatted as a valid `GoalAnswer<string>` object, this can be passed to any component that
 * implement `IGoalsComponent`.
 */
export async function executeCommand(client: CoqLspClient, command: string): Promise<CoqGoalAnswer<string>> {
    try {
        const { goalsRes, runRes, document } = await executeCommandBase(client, command);
        // This should form a valid `GoalAnswer<string>`
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

/**
 * Execute `command` using client `client` and return the full output, that is, the goal after executing the command (`GoalConfig`, contains only goals information) and the result of
 * running the command (`RunResult`, this includes messages and whether the proof was finished running `command`)
 * @param client The client to use when executing the command.
 * @param command The command/tactic to execute. It is allowed to execute multiple tactics/commands by seperating them using `.`'s.
 * @returns The full output of running `command` using `client`.
 */
export async function executeCommandFullOutput(client: CoqLspClient, command: string): Promise<GoalConfig<string> & RunResult<number>> {
    try {
        const { goalsRes, runRes } = await executeCommandBase(client, command);
        return { ...goalsRes, ...runRes };
    } catch (error) {
        throw new Error(`Error when trying to execute command '${command}': ${error}`);
    }
}
