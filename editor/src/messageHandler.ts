import { Completion, HistoryChange, InputAreaStatus, OffsetDiagnostic, ThemeStyle } from "@impermeable/waterproof-editor";
import { Message, MessageType, ServerStatus } from "../../shared";

export interface MessageHandlerEditor {
	init: (value: string, version: number) => void;
	insertSymbol: (symbolUnicode: string) => void;
	handleSnippet: (template: string) => void;
	refreshDocument: (value: string, version: number) => void;
	replaceRange: (start: number, end: number, text: string) => void;
	handleCompletions: (completions: Completion[]) => void;
	setInputAreaStatus: (statuses: InputAreaStatus[]) => void;
	setShowLineNumbers: (show: boolean) => void;
	setShowMenuItems: (show: boolean) => void;
	handleHistoryChange: (historyChange: HistoryChange) => void;
	updateLockingState: (teacherModeEnabled: boolean) => void;
	removeBusyIndicators: () => void;
	reportProgress: (at: number, numberOfLines: number, label: string) => void;
	setBusyIndicator: (from: number) => void;
	setActiveDiagnostics: (diagnostics: Array<OffsetDiagnostic>) => void;
	startSpinner: () => void;
	stopSpinner: () => void;
	updateNodeViewThemes: (theme: ThemeStyle) => void;
}

export function handleEditorMessage(editor: MessageHandlerEditor, msg: Message): void {
	switch (msg.type) {
		case MessageType.init:
			editor.init(msg.body.value, msg.body.version);
			break;
		case MessageType.insert:
			// Insert symbol message, retrieve the symbol from the message.
			{
				const { symbolUnicode } = msg.body;
				if (msg.body.type === "tactics") {
					// `symbolUnicode` stores the tactic template.
					if (!symbolUnicode) { console.error("no template provided for snippet"); return; }
					editor.handleSnippet(symbolUnicode);
				} else {
					editor.insertSymbol(symbolUnicode);
				}
				break;
			}
		case MessageType.refreshDocument:
				editor.refreshDocument(msg.body.value, msg.body.version);
				break;
		case MessageType.replaceRange:
			{
				const { start, end, text } = msg.body;
				editor.replaceRange(start, end, text);
				break;
			}
		case MessageType.setAutocomplete:
			// Handle autocompletion
			editor.handleCompletions(msg.body);
			break;
		case MessageType.qedStatus:
			{
				const statuses = msg.body; // one status for each input area, in order
				editor.setInputAreaStatus(statuses);
				break;
			}
		case MessageType.setShowLineNumbers:
			{
				const show = msg.body;
				editor.setShowLineNumbers(show);
				break;
			}
		case MessageType.setShowMenuItems:
			{
				const show = msg.body;
				editor.setShowMenuItems(show);
				break;
			}
		case MessageType.editorHistoryChange:
			editor.handleHistoryChange(msg.body);
			break;
		case MessageType.teacher:
			editor.updateLockingState(msg.body);
			break;
		case MessageType.progress:
			{
				const { numberOfLines, progress } = msg.body;
				if (progress.length === 0) {
					editor.removeBusyIndicators();
					editor.reportProgress(numberOfLines, numberOfLines, "File verified");
				} else {
					const at = progress[0].range.start.line + 1;
					editor.reportProgress(at, numberOfLines, `Verified file up to line: ${at}`);
				}
				break;
			}
		case MessageType.executionInfo:
			{
				const range = msg.body;
				editor.setBusyIndicator(range.from);
				break;
			}
		case MessageType.diagnostics:
			editor.setActiveDiagnostics(msg.body.positionedDiagnostics);
			break;
		case MessageType.serverStatus:
			{
				const status: ServerStatus = msg.body;
				if (status.status === "Busy") {
					editor.startSpinner();
				} else {
					editor.stopSpinner();
				}
				break;
			}
		case MessageType.themeUpdate:
			editor.updateNodeViewThemes(msg.body.theme);
			break;
		default:
			// If we reach this 'default' case, then we have encountered an unknown message type.
			console.log(`[WEBVIEW] Unrecognized message type '${msg.type}'`);
			break;
	}
}
