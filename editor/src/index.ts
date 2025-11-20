import { FileFormat, Message, MessageType } from "../../shared";
import { defaultToMarkdown, markdown, WaterproofEditor, WaterproofEditorConfig } from "@impermeable/waterproof-editor";
// TODO: The tactics completions are static, we want them to be dynamic (LSP supplied and/or configurable when the editor is running)
import tactics from "../../completions/tactics.json";
import symbols from "../../completions/symbols.json";

// import style sheet and fonts from waterproof-editor
import "@impermeable/waterproof-editor/styles.css"
import { vFileParser } from "./document-construction/vFile";
import { coqdocToMarkdown } from "./coqdoc";
import { topLevelBlocksLean, topLevelBlocksMV } from "./document-construction/construct-document";
import { tagConfigurationV } from "./vFileConfiguration";
import { tagConfigurationLean } from "./leanFileConfiguration";

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
		completions: format === FileFormat.Lean ? [] : tactics,
		symbols: symbols,
		api: {
			executeHelp() {
				codeAPI.postMessage({ type: MessageType.command, body: { command: "Help.", time: (new Date()).getTime() } });
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
		// documentConstructor: format === FileFormat.MarkdownV ? topLevelBlocksMV : topLevelBlocksV,
		documentConstructor:
			format === FileFormat.MarkdownV ? topLevelBlocksMV
				: (format === FileFormat.RegularV) ? vFileParser : topLevelBlocksLean,
		// documentConstructor: format === FileFormat.MarkdownV ? doc => markdownParser(doc, "coq") : vFileParser,
		toMarkdown: (format === FileFormat.MarkdownV || format === FileFormat.Lean) ? defaultToMarkdown : coqdocToMarkdown,
		markdownName: (format === FileFormat.MarkdownV || format === FileFormat.Lean) ? "Markdown" : "coqdoc",
		tagConfiguration: format === FileFormat.MarkdownV ? markdown.configuration("coq")
			: (format === FileFormat.RegularV) ? tagConfigurationV : tagConfigurationLean,
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
	const format = document.body.getAttribute("format") as FileFormat;

	// Create the editor, passing it the vscode api and the editor and content HTML elements.
	const cfg = createConfiguration(format, codeAPI);
	const editor = new WaterproofEditor(editorElement, cfg);

	//@ts-expect-error For now, expose editor in the window. Allows for calling editorInstance methods via the debug console.
	window.editorInstance = editor;

	// Register event listener for communication between extension and editor
	window.addEventListener("message", (event: MessageEvent<Message>) => {
		const msg = event.data;

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
						const template = symbolUnicode;
						editor.handleSnippet(template);
					} else {
						editor.insertSymbol(symbolUnicode);
					}
					break;
				}
			case MessageType.setAutocomplete:
				// Handle autocompletion
				editor.handleCompletions(msg.body);
				break;
			case MessageType.qedStatus:
				{
					const statuses = msg.body;  // one status for each input area, in order
					editor.updateQedStatus(statuses);
					break;
				}
			case MessageType.setShowLineNumbers:
				{
					const show = msg.body;
					editor.setShowLineNumbers(show);
					break;
				}
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
				{
					const progressParams = msg.body;
					editor.updateProgressBar(progressParams);
					break;
				}
			case MessageType.diagnostics:
				{
					const diagnostics = msg.body;
					editor.parseCoqDiagnostics(diagnostics);
					break;
				}
			case MessageType.serverStatus:
				{
					const status = msg.body;
					editor.updateServerStatus(status);
					break;
				}
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
	codeAPI.postMessage({ type: MessageType.ready });
};
