import { RequestType } from "vscode-languageclient";
import { GoalConfig } from "../../lib/types";

export interface RunOpts {
    memo?: boolean;
    hash?: boolean;
}

export type RunResult<ResType> = {
    st : ResType;
    hash?: number;
    proof_finished: boolean;
    feedback: [number, string][];
}

export type GetStateAtPosParams = { 
    uri : string
    opts ?: RunOpts;
    position: { character: number, line: number };
}

export type RunParams = {
    opts?: RunOpts;
    st: number;
    tac: string;
}

export interface GoalParams {
    st: number;
}

export const goalsReq = new RequestType<GoalParams, GoalConfig<string>, void>("petanque/goals");
export const runReq = new RequestType<RunParams, RunResult<number>, void>("petanque/run");
export const getStateAtPosReq = new RequestType<GetStateAtPosParams, RunResult<number>, void>("petanque/get_state_at_pos");
