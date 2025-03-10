import { Completion } from "@codemirror/autocomplete";

import { Message, MessageType } from "../../shared";
import { Editor } from "./kroqed-editor";
import { COQ_CODE_PLUGIN_KEY } from "./kroqed-editor/codeview/coqcodeplugin";

/**
 * Very basic representation of the acquirable VSCodeApi.
 * At least supports `postMessage(message: Message)`.
 */
interface VSCodeAPI {
	postMessage: (message: Message) => void;
}

window.onload = () => {
	// Get HTML DOM elements
	const editorElement = document.querySelector<HTMLElement>("#editor");

	if (editorElement == null) {
		throw Error("Editor element cannot be null (no element with id 'editor' found)");
	}

	const vscode = acquireVsCodeApi() as VSCodeAPI;
	if (vscode == null) {
		throw Error("Could not acquire the vscode api.");
		// TODO: maybe sent some sort of test message?
	}

	// Create the editor, passing it the vscode api and the editor and content HTML elements.
	const theEditor = new Editor(vscode, editorElement);

	window.addEventListener("message", (event: MessageEvent<Message>) => {
		const msg = event.data;

		switch(msg.type) {
			case MessageType.init:
				// @ts-expect-error TODO: Fix this
				theEditor.init(msg.body.value, msg.body.format, msg.body.version);
				break;
			case MessageType.insert:
				// Insert symbol message, retrieve the symbol from the message.
				{ 
				// @ts-expect-error TODO: Fix this
				const { symbolUnicode, symbolLatex } = msg.body;
				// @ts-expect-error TODO: Fix this
				if (msg.body.type === "tactics") {
					// `symbolUnicode` stores the tactic template.
					if (!symbolUnicode) { console.error("no template provided for snippet"); return; }
					const template = symbolUnicode;
					theEditor.handleSnippet(template);
				} else {
					theEditor.insertSymbol(symbolUnicode, symbolLatex);
				}
				break; }
			case MessageType.setAutocomplete:
				// Handle autocompletion
				{ const state = theEditor.state;
				if (!state) break;
				// @ts-expect-error TODO: Fix this
				const completions: Completion[] = msg.body;
				// Apply autocomplete to all coq cells
				COQ_CODE_PLUGIN_KEY
					.getState(state)
					?.activeNodeViews
					?.forEach(codeBlock => codeBlock.handleNewComplete(completions));
				break; }
			case MessageType.fatalError:
				// TODO: show skull
				break;
			case MessageType.editorHistoryChange:
				// @ts-expect-error TODO: Fix this
				theEditor.handleHistoryChange(msg.body);
				break;
			default:
				theEditor.handleMessage(msg);
				break;
		}
	});

	// Start the editor
	theEditor.post({type: MessageType.ready});
};
