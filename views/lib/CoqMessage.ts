import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";

export interface RenderGoals {
  type: "renderGoals";
  body: GoalAnswer<PpString>;
}
export interface WaitingForInfo {
  type: "waitingForInfo";
  body: GoalRequest;
}
export interface InfoError {
  type: "infoError";
  body: any;
}
//a message designed for Coq that extends MessageEvent
export interface CoqMessageEvent extends MessageEvent {
  data: RenderGoals | WaitingForInfo | InfoError;
}
