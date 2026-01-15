import { FileFormat, Message, MessageType } from "../../shared";
import { defaultToMarkdown, markdown, ThemeStyle, WaterproofEditor, WaterproofEditorConfig } from "@impermeable/waterproof-editor";
// TODO: The tactics completions are static, we want them to be dynamic (LSP supplied and/or configurable when the editor is running)
import tactics from "../../completions/tactics.json";
import symbols from "../../completions/symbols.json";

// import style sheet and fonts from waterproof-editor
import "@impermeable/waterproof-editor/styles.css"
import { vFileParser } from "./document-construction/vFile";
import { coqdocToMarkdown } from "./coqdoc";
import { tagConfigurationV } from "./vFileConfiguration";
import { highlight_dark, highlight_light, wpLanguageSupport } from "./lang-pack";

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
			}
		},
		// documentConstructor: format === FileFormat.MarkdownV ? topLevelBlocksMV : topLevelBlocksV,
		documentConstructor: format === FileFormat.MarkdownV ? v => markdown.parse(v, { language: "coq" }) : vFileParser,
		// documentConstructor: format === FileFormat.MarkdownV ? doc => markdownParser(doc, "coq") : vFileParser,
		toMarkdown: format === FileFormat.MarkdownV ? defaultToMarkdown : coqdocToMarkdown,
		markdownName: format === FileFormat.MarkdownV ? "Markdown" : "coqdoc",
		tagConfiguration: format === FileFormat.MarkdownV ? markdown.configuration("coq") : tagConfigurationV,
		disableMarkdownFeatures: format === FileFormat.RegularV ? ["code"] : [],
		languageConfig: {
			highlightDark: highlight_dark,
			highlightLight: highlight_light,
			languageSupport: wpLanguageSupport
		}
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
	const format = document.body.getAttribute("format") === "markdownv" ? FileFormat.MarkdownV : FileFormat.RegularV;

	// Create the editor, passing it the vscode api and the editor and content HTML elements.
	const cfg = createConfiguration(format, codeAPI);
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

	//@ts-expect-error For now, expose editor in the window. Allows for calling editorInstance methods via the debug console.
	window.editorInstance = editor;

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
				editor.setInputAreaStatus(statuses);
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
			case MessageType.teacher:
				editor.updateLockingState(msg.body);
				break;
			case MessageType.progress:
				{
					const {numberOfLines, progress} = msg.body;
					const at = progress[0].range.start.line + 1;
					if (at === numberOfLines) {
						editor.reportProgress(at, numberOfLines, "File verified");
					} else {
						editor.reportProgress(at, numberOfLines, `Verified file up to line: ${at}`);
					}
					break;
				}
			case MessageType.diagnostics:
				{ editor.setActiveDiagnostics(msg.body.positionedDiagnostics);
				break; }
			case MessageType.serverStatus:
				{
					const {status} = msg.body;
					if (status === "Busy") {
						editor.startSpinner();
					} else {
						editor.stopSpinner();
					}
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
	codeAPI.postMessage({type: MessageType.ready});
};
