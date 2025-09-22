import { RequestType } from "vscode-languageclient";
import { GoalConfig } from "../../lib/types";

export interface Run_opts {
    memo?: boolean;
    hash?: boolean;
}

export interface Run_result<res> {
    st : res;
    hash?: number;
    proof_finished: boolean;
    feedback: [number, string][];
}

export interface GetStateAtPosParams { 
    uri : string
    opts ?: Run_opts;
    position: {offset: number, character: number, line: number};
}

export interface RunParams {
    opts?: Run_opts;
    st: number;
    tac: string;
}

export interface GoalsParams {
    st: number;
}

// export interface Info {
//     kind: string;
//     range?: Range;
//     offset: [number, number];
//     raw_text
// }

// export interface PremiseResponse {

// }

export const goalsReq = new RequestType<GoalsParams, GoalConfig<string>, void>("petanque/goals");
export const runReq = new RequestType<RunParams, Run_result<number>, void>("petanque/run");
export const getStateAtPosReq = new RequestType<GetStateAtPosParams, Run_result<number>, void>("petanque/get_state_at_pos");
// export const premisesReq = new RequestType<GoalsParams, any, void>("petanque/premises");
// export const astAtPosReq = new RequestType<{uri: string, position: any}, any, void>("petanque/ast_at_pos");
// export const ast = new RequestType<{}