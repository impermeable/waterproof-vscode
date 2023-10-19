import { Message } from "../../../../../shared";

/**
 * Very basic representation of the acquirable VSCodeApi.
 * At least supports `postMessage(message: Message)`.
 */
export interface VSCodeAPI {
	postMessage: (message: Message) => void;
}