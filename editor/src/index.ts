import { Completion } from "@codemirror/autocomplete";

import { Message, MessageType } from "../../shared";
import { Editor } from "./kroqed-editor";
import { COQ_CODE_PLUGIN_KEY } from "./kroqed-editor/codeview/coqcodeplugin";
import { VSCodeAPI } from "./kroqed-editor/common/types";
import { KeyBinding } from "../../shared/Messages";

window.onload = () => {
	// Get HTML DOM elements
	const editorElement = document.querySelector<HTMLElement>("#editor");
	const contentElement = document.querySelector<HTMLElement>("#editor-content");

	if (editorElement == null) {
		throw Error("Editor element cannot be null (no element with id 'editor' found)");
	} else if (contentElement == null) {
		throw Error("Content element cannot be null (no element with id 'editor-content' found)");
	}

	//@ts-ignore
	const vscode = acquireVsCodeApi() as VSCodeAPI;
	if (vscode == null) {
		throw Error("Could not acquire the vscode api.");
		// TODO: maybe sent some sort of test message?
	}

	// Create the editor, passing it the vscode api and the editor and content HTML elements.
	const theEditor = new Editor(vscode, editorElement, contentElement);

	window.addEventListener("message", (event: MessageEvent) => {
		const msg = event.data as Message; // TODO: This should be error checked!

		switch(msg.type) {
			case MessageType.init:
				theEditor.init(msg.body.value, msg.body.format, msg.body.version);
				break;
			case MessageType.insert:
				// Insert symbol message, retrieve the symbol from the message.
				const symbolUnicode = msg.body.symbolUnicode;
				const symbolLaTeX = msg.body.symbolLatex;
				theEditor.insertSymbol(symbolUnicode, symbolLaTeX);
				break;
			case MessageType.setAutocomplete:
				// Handle autocompletion
				const state = theEditor.state;
				if (!state) break;
				const completions: Completion[] = msg.body;
				// Apply autocomplete to all coq cells
				COQ_CODE_PLUGIN_KEY
					.getState(state)
					?.activeNodeViews
					?.forEach(codeBlock => codeBlock.handleNewComplete(completions));
				break;
			case MessageType.fatalError:
				// TODO: show skull
				break;
			case MessageType.execKeyBinding:
				theEditor.doKeyBinding(msg.body as KeyBinding);
				break;
			default:
				theEditor.handleMessage(msg);
				break;
		}
	});

	// Start the editor
	theEditor.post({type: MessageType.ready});
};
