import { RequestType, NotificationType } from "vscode-languageclient";
import { CoqGoalRequest, CoqGoalAnswer, PpString, CoqServerStatus } from "../../../lib/types";
import { FileProgressParams } from "../requestTypes";

/**
 * LSP request to obtain the goals at a specific point in the doc.
 */
export const coqGoalRequestType = new RequestType<CoqGoalRequest, CoqGoalAnswer<PpString>, void>("proof/goals");

/**
 * LSP notification regarding the progress on processing the document server side
 */
export const coqFileProgressNotificationType = new NotificationType<FileProgressParams>("$/coq/fileProgress");

/**
 * Notification type for the coq-lsp specific `serverStatus` notification. Returns a `CoqServerStatus` object that
 * can be either Busy or Idle.
 */
export const coqServerStatusNotificationType = new NotificationType<CoqServerStatus>("$/coq/serverStatus");
