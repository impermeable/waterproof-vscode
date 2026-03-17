import { RequestType, NotificationType } from "vscode-languageclient";
import { RocqGoalRequest, RocqGoalAnswer, PpString, RocqServerStatus } from "../../../lib/types";
import { FileProgressParams } from "../requestTypes";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const coqGoalRequestType = new RequestType<RocqGoalRequest, RocqGoalAnswer<PpString>, void>("proof/goals");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const coqFileProgressNotificationType = new NotificationType<FileProgressParams>("$/coq/fileProgress");

/**
 * LSP notification regarding the execution information of the sentence currently being checked.
 */
export type ExecutionInformationParams = {
    textDocument: { uri: string; version: number };
    range: { start: { line: number; character: number }; end: { line: number; character: number } };
};
export const executionInformationNotificationType = new NotificationType<ExecutionInformationParams>("$/coq/executionInformation");

/**
 * Notification type for the coq-lsp specific `serverStatus` notification. Returns a `CoqServerStatus` object that
 * can be either Busy or Idle.
 */
export const coqServerStatusNotificationType = new NotificationType<RocqServerStatus>("$/coq/serverStatus");
