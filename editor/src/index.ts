import { FileFormat, Message, MessageType } from "../../shared";
import { WaterproofEditor, WaterproofEditorConfig } from "./waterproof-editor";
// TODO: Move this to a types location.
import { TextDocMappingMV, TextDocMappingV } from "./mapping";
import { blocksFromMV, blocksFromV } from "./document-construction/construct-document";

/**
 * Very basic representation of the acquirable VSCodeApi.
 * At least supports `postMessage(message: Message)`.
 */
interface VSCodeAPI {
	postMessage: (message: Message) => void;
}

function createConfiguration(format: FileFormat, codeAPI: VSCodeAPI) {
	// Create the WaterproofEditorConfig object
	const cfg: WaterproofEditorConfig = {
		api: {
			executeHelp() {
				codeAPI.postMessage({ type: MessageType.command, body: { command: "Help.", time: (new Date()).getTime()} });
			},
			executeCommand(command: string, time: number) {
				codeAPI.postMessage({ type: MessageType.command, body: { command, time } });
			},
			editorReady() {
				codeAPI.postMessage({ type: MessageType.editorReady });
			},
			documentChange(change) {
				codeAPI.postMessage({ type: MessageType.docChange, body: change });
			},
			applyStepError(errorMessage) {
				codeAPI.postMessage({ type: MessageType.applyStepError, body: errorMessage });
			},
			cursorChange(cursorPosition) {
				codeAPI.postMessage({ type: MessageType.cursorChange, body: cursorPosition });
			},
			lineNumbers(linenumbers, version) {
				codeAPI.postMessage({ type: MessageType.lineNumbers, body: { linenumbers, version } });
			},
		},
		documentConstructor: format === FileFormat.MarkdownV ? blocksFromMV : blocksFromV,
		// TODO: For now assuming we are constructing an mv file editor.
		mapping: format === FileFormat.MarkdownV ? TextDocMappingMV : TextDocMappingV
	}

	return cfg;
}

window.onload = () => {
	// Get HTML DOM elements
	const editorElement = document.querySelector<HTMLElement>("#editor");

	if (editorElement == null) {
		throw Error("Editor element cannot be null (no element with id 'editor' found)");
	}

	const codeAPI = acquireVsCodeApi() as VSCodeAPI;
	if (codeAPI == null) {
		throw Error("Could not acquire the vscode api.");
		// TODO: maybe sent some sort of test message?
	}


	// Create the editor, passing it the vscode api and the editor and content HTML elements.
	const cfg = createConfiguration(FileFormat.MarkdownV, codeAPI);
	const editor = new WaterproofEditor(editorElement, cfg);

	// Register event listener for communication between extension and editor
	window.addEventListener("message", (event: MessageEvent<Message>) => {
		const msg = event.data;

		switch(msg.type) {
			case MessageType.init:
				editor.init(msg.body.value, msg.body.format, msg.body.version);
				break;
			case MessageType.insert:
				// Insert symbol message, retrieve the symbol from the message.
				{
				const { symbolUnicode, symbolLatex } = msg.body;
				if (msg.body.type === "tactics") {
					// `symbolUnicode` stores the tactic template.
					if (!symbolUnicode) { console.error("no template provided for snippet"); return; }
					const template = symbolUnicode;
					editor.handleSnippet(template);
				} else {
					editor.insertSymbol(symbolUnicode, symbolLatex);
				}
				break; }
			case MessageType.setAutocomplete:
				// Handle autocompletion
				editor.handleCompletions(msg.body);
				break;
			case MessageType.qedStatus:
				{ const statuses = msg.body;  // one status for each input area, in order
				editor.updateQedStatus(statuses);
				break; }
			case MessageType.setShowLineNumbers:
				{ const show = msg.body;
				editor.setShowLineNumbers(show);
				break; }
			case MessageType.setShowMenuItems:
				{ const show = msg.body; editor.setShowMenuItems(show); break; }
			case MessageType.editorHistoryChange:
				editor.handleHistoryChange(msg.body);
				break;
			case MessageType.lineNumbers:
				editor.setLineNumbers(msg.body);
				break;
			case MessageType.teacher:
				editor.updateLockingState(msg.body);
				break;
			case MessageType.progress:
				{ const progressParams = msg.body;
				editor.updateProgressBar(progressParams);
				break; }
			case MessageType.diagnostics:
				{ const diagnostics = msg.body;
				editor.parseCoqDiagnostics(diagnostics);
				break; }
			case MessageType.syntax:
				editor.initTacticCompletion(msg.body);
				break;
			default:
				// If we reach this 'default' case, then we have encountered an unknown message type.
				console.log(`[WEBVIEW] Unrecognized message type '${msg.type}'`);
				break;
		}
	});

	// Start the editor
	codeAPI.postMessage({type: MessageType.ready});
};
