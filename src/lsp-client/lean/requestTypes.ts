import { RequestType, NotificationType, DocumentUri, Diagnostic } from "vscode-languageclient";
import { LeanGoalRequest, LeanGoalAnswer } from "../../../lib/types";
import { FileProgressParams } from "../requestTypes";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const leanGoalRequestType = new RequestType<LeanGoalRequest, LeanGoalAnswer, void>("$/lean/plainGoal");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const leanFileProgressNotificationType = new NotificationType<FileProgressParams>("$/lean/fileProgress");

/**
 * The types below come from
 * https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview-api/src/lspTypes.ts
 */
export interface LeanPublishDiagnosticsParams {
    uri: DocumentUri;
    version?: number;
    diagnostics: LeanDiagnostic[];
}

export interface LeanDiagnostic extends Diagnostic {
    fullRange?: Range;
    isSilent?: boolean;
    leanTags?: LeanTag[];
}

export enum LeanTag {
    UnsolvedGoals = 1,
    GoalsAccomplished = 2,
}
