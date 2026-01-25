import { FileFormat, Message, MessageType } from "../../shared";
import { ThemeStyle, WaterproofEditor, WaterproofEditorConfig } from "@impermeable/waterproof-editor";
// TODO: Move this to a types location.
import { TextDocMappingMV, TextDocMappingV } from "./mapping";
import { blocksFromMV, blocksFromV } from "./document-construction/construct-document";
// TODO: The tactics completions are static, we want them to be dynamic (LSP supplied and/or configurable when the editor is running)
import tactics from "../../completions/tactics.json";
import symbols from "../../completions/symbols.json";

// import style sheet and fonts from waterproof-editor
import "@impermeable/waterproof-editor/styles.css";
// import the style sheet mapping waterproof style properties to vscode styles
import "./vscodemapping.css";

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
		completions: tactics,
		symbols: symbols,
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
			viewportHint(start, end) {
				codeAPI.postMessage({ type: MessageType.viewportHint, body: { start, end } });
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
	// Retrieve the current theme style from the attribute 'data-theme-kind'
	// attached to the editor element. This allows us to set the initial theme kind
	// rather than waiting for the themestyle message to arrive.
	const themeStyle: ThemeStyle = (() => {
		const value = editorElement.getAttribute("data-theme-kind");
		if (value === null) {
			throw Error("Could not get theme style from editor element");
		}

		switch (value) {
			case "dark": return ThemeStyle.Dark;
			case "light": return ThemeStyle.Light;
			default: throw Error("Invalid theme encountered");
		}
	})();
	const editor = new WaterproofEditor(editorElement, cfg, themeStyle);

	// Register event listener for communication between extension and editor
	window.addEventListener("message", (event: MessageEvent<Message>) => {
		const msg = event.data;

		switch(msg.type) {
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
					const template = symbolUnicode;
					editor.handleSnippet(template);
				} else {
					editor.insertSymbol(symbolUnicode);
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
				{ editor.setActiveDiagnostics(msg.body.positionedDiagnostics);
				break; }
			case MessageType.serverStatus:
				{ const status = msg.body;
				editor.updateServerStatus(status);
				break; }
			case MessageType.themeUpdate:
				editor.updateNodeViewThemes(msg.body);
				break;
			default:
				// If we reach this 'default' case, then we have encountered an unknown message type.
				console.log(`[WEBVIEW] Unrecognized message type '${msg.type}'`);
				break;
		}
	});
	let timeoutHandle: number | undefined;
	window.addEventListener('scroll', (_event) => {
		if (timeoutHandle === undefined) {
			timeoutHandle = window.setTimeout(() => {
				editor.handleScroll(window.innerHeight);
				timeoutHandle = undefined;
			}, 100);
		}
	});

	// Start the editor
	codeAPI.postMessage({type: MessageType.ready});
};
