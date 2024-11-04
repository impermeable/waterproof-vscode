import { mathPlugin, mathSerializer } from "@benrbray/prosemirror-math";
import { deleteSelection, selectParentNode } from "prosemirror-commands";
import { keymap } from "prosemirror-keymap";
import { ResolvedPos, Schema, Node as ProseNode } from "prosemirror-model";
import { AllSelection, EditorState, NodeSelection, Plugin, Selection, TextSelection, Transaction } from "prosemirror-state";
import { ReplaceAroundStep, ReplaceStep, Step } from "prosemirror-transform";
import { EditorView } from "prosemirror-view";
import { createProseMirrorDocument } from "./prosedoc-construction/construct-document";

import { DocChange, FileFormat, LineNumber, Message, MessageType, QedStatus, SimpleProgressParams, WrappingDocChange } from "../../../shared";
import { COQ_CODE_PLUGIN_KEY, coqCodePlugin } from "./codeview/coqcodeplugin";
import { createHintPlugin } from "./hinting";
import { INPUT_AREA_PLUGIN_KEY, inputAreaPlugin } from "./inputArea";
import { TheSchema } from "./kroqed-schema";
import { TextDocMapping } from "./mappingModel";
import { REAL_MARKDOWN_PLUGIN_KEY, coqdocPlugin, realMarkdownPlugin } from "./markup-views";
import { menuPlugin } from "./menubar";
import { MENU_PLUGIN_KEY } from "./menubar/menubar";
import { PROGRESS_PLUGIN_KEY, progressBarPlugin } from "./progressBar";
import { FileTranslator } from "./translation";
import { createContextMenuHTML } from "./context-menu";
import { initializeTacticCompletion } from "./autocomplete/tactics";

// CSS imports
import "katex/dist/katex.min.css";
import "prosemirror-view/style/prosemirror.css";
import "./styles";
import { UPDATE_STATUS_PLUGIN_KEY, updateStatusPlugin } from "./qedStatus";
import { CodeBlockView } from "./codeview/nodeview";
import { InsertionPlace, cmdInsertCoq, cmdInsertLatex, cmdInsertMarkdown } from "./commands";
import { DiagnosticMessage } from "../../../shared/Messages";
import { DiagnosticSeverity, ThemeIcon } from "vscode";
import { OS } from "./osType";
import { checkPrePost } from "./file-utils";

/**
 * Very basic representation of the acquirable VSCodeApi.
 * At least supports `postMessage(message: Message)`.
 */
interface VSCodeAPI {
	postMessage: (message: Message) => void;
}

/** Type that contains a coq diagnostics object fit for use in the ProseMirror editor context. */
type DiagnosticObjectProse = {message: string, start: number, end: number, $start: ResolvedPos, $end: ResolvedPos, severity: DiagnosticSeverity};

/**
 * Class that contains the editor component.
 *
 * Stores the state of the editor.
 */
export class Editor {
	// The vscode api
	private _api: VSCodeAPI;

	// The schema used in this prosemirror editor.
	private _schema: Schema;

	// The editor and content html elements.
	private _editorElem: HTMLElement;

	// The prosemirror view
	private _view: EditorView | undefined;

	// The file translator in use.
	private _translator: FileTranslator | undefined;

	// The file document mapping
	private _mapping: TextDocMapping | undefined;

	// User operating system.
	private readonly _userOS;
	private _filef: any;

	private currentProseDiagnostics: Array<DiagnosticObjectProse>;

	constructor (vscodeapi: VSCodeAPI, editorElement: HTMLElement) {
		this._api = vscodeapi;
		this._schema = TheSchema;
		this._editorElem = editorElement;

		const userAgent = window.navigator.userAgent;
		this._userOS = OS.Unknown;
		if (userAgent.includes("Win")) this._userOS = OS.Windows;
		if (userAgent.includes("Mac")) this._userOS = OS.MacOS;
		if (userAgent.includes("X11")) this._userOS = OS.Unix;
		if (userAgent.includes("Linux")) this._userOS = OS.Linux;

		const theContextMenu = createContextMenuHTML(this);


		document.body.appendChild(theContextMenu);

		// Setup the custom context menu
		document.addEventListener("click", (ev) => {
			// Handle a 'left mouse click'
			// console.log("LMB");
			theContextMenu.style.display = "none";
		});

		document.addEventListener("contextmenu", (ev) => {
			// Handle a 'right mouse click'
			// We call preventDefault to prevent the default context menu from showing
			ev.preventDefault();
			// After this we display our own context menu
			const x: string = `${ev.pageX}px`;
			const y: string = `${ev.pageY}px`;
			theContextMenu.style.position = "absolute";
			theContextMenu.style.left = x;
			theContextMenu.style.top = y;
			theContextMenu.style.display = "block";
		})
	}

	init(content: string, fileFormat: FileFormat, version: number = 1) {
		// Initialize the file translator given the fileformat.
		if(this._view) {
			if (this._mapping && this._mapping.version == version) return;
			this._view.dispatch(this._view.state.tr.setMeta(MENU_PLUGIN_KEY, "remove"));
			// Hack to forcefully remove the 'old' menubar
			document.querySelector(".menubar")?.remove();
			document.querySelector(".progress-bar")?.remove();
			document.querySelector(".spinner-container")?.remove();
			this._view.dom.remove();
		}

		if (fileFormat === FileFormat.MarkdownV) {
			document.body.classList.add("mv");
		}

		this._filef = fileFormat;
		this._translator = new FileTranslator(fileFormat);

		let newContent = checkPrePost(content, (msg: Message) => {
			this.post(msg);
		});
		if (newContent !== content) version = version + 1;

		let parsedContent = this._translator.toProsemirror(newContent);
		// this._contentElem.innerHTML = parsedContent;

		const proseDoc = createProseMirrorDocument(newContent, fileFormat);

		this._mapping = new TextDocMapping(fileFormat, parsedContent, version);
		this.createProseMirrorEditor(proseDoc);

		/** Ask for line numbers */
		this.sendLineNumbers();

		// notify extension that editor has loaded
		this.post({ type: MessageType.editorReady });
	}

	get state(): EditorState | undefined {
		return this._view?.state;
	}

	createProseMirrorEditor(proseDoc: ProseNode) {
		// Shadow this variable _userOS.
		const userOS = this._userOS;
		let view = new EditorView(this._editorElem, {
			state: this.createState(proseDoc),
			clipboardTextSerializer: (slice) => { return mathSerializer.serializeSlice(slice) },
			dispatchTransaction: ((tr) => {
				// Called on every transaction.
				view.updateState(view.state.apply(tr));
				let step : Step | undefined = undefined;
				for (step of tr.steps) {
					if (step instanceof ReplaceStep || step instanceof ReplaceAroundStep) {
						if (this._mapping === undefined) throw new Error(" Mapping is undefined, cannot synchronize with vscode");
						try {
							let obj: DocChange | WrappingDocChange = this._mapping.stepUpdate(step); // Get text document update
							this.post({type: MessageType.docChange, body: obj});
						} catch (error) {
							console.error(error.message);


							// Send message to VSCode that an error has occured
							this.post({type: MessageType.applyStepError, body: error.message})

							// Set global locking mode
							const tr = view.state.tr;
							tr.setMeta(INPUT_AREA_PLUGIN_KEY,"ErrorMode");
							tr.setSelection(new AllSelection(view.state.doc));
							view.updateState(view.state.apply(tr));

							// We ensure this transaction is not applied
							return;
						}

					}
				}
				if (tr.selectionSet && tr.selection instanceof TextSelection) {
					this.updateCursor(tr.selection);
				} else if (tr.getMeta(REAL_MARKDOWN_PLUGIN_KEY)) {
					// Set the cursor position from a markdown cell
					this.updateCursor(tr.getMeta(REAL_MARKDOWN_PLUGIN_KEY));
				}

				if (step !== undefined) this.sendLineNumbers();
			}),
			handleKeyDown(view, e) {
				// Stop certain events from propagating
				if ((userOS == OS.Windows && e.ctrlKey) ||
					(userOS == OS.MacOS && e.metaKey)) {
					if (["q", "m", "Enter", "Space", ".", "l", "Q", "M", "L"].includes(e.key)) {
						// Fixes ctrl-q on Windows and cmd-q on MacOs opening weird ctrl-q thingie.
						// when the user wants to make text bold.
						e.stopImmediatePropagation();
					}
				}
				// Prevent any key presses other than backspaces from registering when selecting node
				if (view.state.selection instanceof NodeSelection) {
					e.preventDefault();
				}
			},
			handleDOMEvents: {
				// This function will handle some DOM events before ProseMirror does.
				// 	We use it here to cancel the 'drag' and 'drop' events, since these can
				//  break the editor.
				"dragstart": (view, event) => {
					event.preventDefault();
				},
				"drop": (view, event) => {
					event.preventDefault();
				}
			}
		});
		this._view = view;
	}

	/** Create initial prosemirror state */
	createState(proseDoc: ProseNode): EditorState {
		return EditorState.create({
			schema: this._schema,
			doc: proseDoc,
			plugins: this.createPluginsArray()
		});
	}

	/** Create the array of plugins used by the prosemirror editor */
	createPluginsArray(): Plugin[] {
		return [
			createHintPlugin(this._schema),
			inputAreaPlugin,
			updateStatusPlugin(this),
			mathPlugin,
			realMarkdownPlugin(this._schema),
			coqdocPlugin(this._schema),
			coqCodePlugin,
			progressBarPlugin,
			menuPlugin(this._schema, this._filef, this._userOS),
			keymap({
				"Mod-h": () => {
					this.post({type: MessageType.command, body: "Help.", time: (new Date()).getTime()});
					return true;
				},
				"Backspace": deleteSelection,
				"Delete": deleteSelection,
				"Mod-m": cmdInsertMarkdown(this._schema, this._filef, InsertionPlace.Underneath),
				"Mod-M": cmdInsertMarkdown(this._schema, this._filef, InsertionPlace.Above),
				"Mod-q": cmdInsertCoq(this._schema, this._filef, InsertionPlace.Underneath),
				"Mod-Q": cmdInsertCoq(this._schema, this._filef, InsertionPlace.Above),
				"Mod-l": cmdInsertLatex(this._schema, this._filef, InsertionPlace.Underneath),
				"Mod-L": cmdInsertLatex(this._schema, this._filef, InsertionPlace.Above),
				// We bind Ctrl/Cmd+. to selecting the parent node of the currently selected node.
				"Mod-.": selectParentNode
			})
		];
	}

	handleSnippet(template: string) {
		const view = this._view!!;
		// Get the first selection.
		const from = view.state.selection.from;
		const to = view.state.selection.to;

		// We need to figure out to which codemirror cell this insertion belongs.

		const state = view.state;

		const nodeViews = COQ_CODE_PLUGIN_KEY.getState(state)?.activeNodeViews;
		if (!nodeViews) return;
		const nodeViewsWithPositions = Array.from(nodeViews).map((codeblock) => {
			return {
				codeblock,
				pos: codeblock._getPos()
			}
		});

		let theView: CodeBlockView | undefined = undefined;
		let pos = view.state.doc.content.size;
		for(const obj of nodeViewsWithPositions) {
			if (obj.pos === undefined) continue;
			if(from - obj.pos < pos && obj.pos < from) {
				pos = from - obj.pos;
				theView = obj.codeblock;
			}
		}
		if (!theView) return;
		const insertionPosFrom 	= state.selection.$from.parentOffset;
		const insertionPosTo 	= state.selection.$to.parentOffset;
		theView.handleSnippet(template, insertionPosFrom, insertionPosTo);
	}

	/** Called on every selection update. */
	updateCursor(pos: Selection) : void {
		// If this is not a cursor update return
		if (!(pos instanceof TextSelection)) return;
		if (this._mapping === undefined) throw new Error(" Mapping is undefined, cannot synchronize with vscode");
		this.post({type: MessageType.cursorChange, body: this._mapping.findPosition(pos.$head.pos)});
	}

	/** Called on every transaction update in which the textdocument was modified */
	sendLineNumbers() {
		if (!this._view || COQ_CODE_PLUGIN_KEY.getState(this._view.state) === undefined) return;
		const linenumbers = Array<number>();
		//@ts-ignore
		for (let codeCell of COQ_CODE_PLUGIN_KEY.getState(this._view.state).activeNodeViews) {
			//@ts-ignore
			linenumbers.push(this._mapping?.findPosition(codeCell._getPos() + 1));
		}
		this.post({type: MessageType.lineNumbers, body: {linenumbers, version: this._mapping?.version}});
	}

	/** Called whenever a line number message is received from vscode to update line numbers of codemirror cells */
	setLineNumbers(msg: LineNumber) {
		if (!this._view || !this._mapping || msg.version < this._mapping.version) return;
		let state = COQ_CODE_PLUGIN_KEY.getState(this._view.state);
		if (!state) return;
		const tr = this._view.state.tr.setMeta(COQ_CODE_PLUGIN_KEY, msg);
		this._view.dispatch(tr);
	}

	/**
	 * Insert a symbol at the cursor position (or overwrite the current selection).
	 *
	 * @param symbolUnicode The unicode character to insert.
	 * @param symbolLaTeX The LaTeX command(s) to produce the character.
	 * @returns Whether the operation was a success.
	 */
	insertSymbol(symbolUnicode: string, symbolLaTeX: string): boolean {
		// If there is no view at the moment this is a no-op.
		if (!this._view) return false;
		let state = this._view.state;
		let from = state.selection.from;
		let to = state.selection.to;
		if (REAL_MARKDOWN_PLUGIN_KEY.getState(state)?.cursor) {
			//@ts-ignore
			from = REAL_MARKDOWN_PLUGIN_KEY.getState(state)?.cursor?.from;
			//@ts-ignore
			to = REAL_MARKDOWN_PLUGIN_KEY.getState(state)?.cursor?.to;
		}
		state = this._view.state;
		const trans = state.tr;

		/* TODO: The check that makes sure we are allowed to insert is pretty much the
			same as in `inputArea.ts` and could maybe be improved. */

		const inputAreaPluginState = INPUT_AREA_PLUGIN_KEY.getState(state);

		// Early return if the plugin state is undefined.
		if (inputAreaPluginState === undefined) return false;
		const { locked, globalLock } = inputAreaPluginState;
		// Early return if we are in the global locked mode
		// 	(nothing should be editable anymore)
		if (globalLock) return false;

		// If we are in teacher mode (ie. not locked) than
		// 	 we are always able to insert.
		if (!locked) {
			this.createAndDispatchInsertionTransaction(trans, symbolUnicode, from, to);
			return true;
		}

		const { $from } = state.selection;


		let isEditable = false;
		state.doc.nodesBetween($from.pos, $from.pos, (node) => {
			if (node.type.name === "input") {
				isEditable = true;
			}
		});

		if (!isEditable) return false;

		this.createAndDispatchInsertionTransaction(trans, symbolUnicode, from, to);

		return true;
	}

	private createAndDispatchInsertionTransaction(
		trans: Transaction, textToInsert: string, from: number, to: number) {

		trans = trans.insertText(textToInsert, from, to);
		this._view?.dispatch(trans);
	}

	/**
	 * Called whenever a message describing the configuration of user is sent
	 *
	 * @param isTeacher represents the mode selected by user
	 */
	updateLockingState(isTeacher: boolean) : void {
		if (!this._view) return;
		const state = this._view.state;
		const trans = state.tr;
		trans.setMeta(INPUT_AREA_PLUGIN_KEY,!isTeacher);
		this._view.dispatch(trans);
	}

	updateProgressBar(progressParams: SimpleProgressParams): void {
		if (!this._view) return;
		const state = this._view.state;
		const tr = state.tr;
		tr.setMeta(PROGRESS_PLUGIN_KEY, progressParams);
		this._view.dispatch(tr);
	}

	updateQedStatus(status: QedStatus[]) : void {
		if (!this._view) return;
		const state = this._view.state;
		const tr = state.tr;
		tr.setMeta(UPDATE_STATUS_PLUGIN_KEY, status);
		this._view.dispatch(tr);
	}

	parseCoqDiagnostics(msg: DiagnosticMessage) {
		if (this._mapping === undefined || msg.version < this._mapping.version) return;

		let diagnostics = msg.positionedDiagnostics;
		const map = this._mapping;
		if (this._view === undefined || map === undefined) return;

		// Get the available coq views
		const views = COQ_CODE_PLUGIN_KEY.getState(this._view.state)?.activeNodeViews;
		if (views === undefined) return;
		// Clear the errors
		for (let view of views) view.clearCoqErrors();

		// Convert to inverse mapped positions.
		const doc = this._view.state.doc;
		this.currentProseDiagnostics = new Array<DiagnosticObjectProse>();
		for (let diag of diagnostics) {
			const start = map.findInvPosition(diag.startOffset);
			const end = map.findInvPosition(diag.endOffset);
			if (start >= end) continue;
			this.currentProseDiagnostics.push({
				message: diag.message,
				start,
				$start: doc.resolve(start),
				end,
				$end: doc.resolve(end),
				severity: diag.severity
			});
		}

		// TODO: the below code can probably be optimized a bit
	    for (const diag of this.currentProseDiagnostics) {
			if (diag.start > diag.end) {
				console.error("We do not support errors for which the start position is greater than the end postion.");
				continue;
			}

			let viewFound : boolean = false;
			for (const view of views) {
				const pos : number | undefined = view._getPos();
				if (pos === undefined) continue;
				const viewSize : number | undefined = this._view.state.doc.nodeAt(pos)?.nodeSize
				if (viewSize === undefined) continue;
				const endPos : number = pos + viewSize - 1;
				if (diag.start < endPos && diag.end > pos) {
					viewFound = true;
					const startPos = Math.max(diag.start, pos + 1);
					const finalPos = Math.min(diag.end, endPos);
					try {
						view.addCoqError(startPos - pos - 1, finalPos - pos - 1, diag.message, diag.severity);
					}
					catch (e) {
						console.error(`Could not display diagnostic information for codeview at position ${pos}:`);
						console.error(e);
					}
				}
			}

			if (!viewFound) throw new Error("Diagnostic message does not match any coqblock");
		}
	}

	public getDiagnosticsInRange(low: number, high: number): Array<DiagnosticObjectProse> {
		return this.currentProseDiagnostics.filter((value) => {
			return ((low <= value.end) && (value.start <= high) && (value.severity) <= 1);
		});
	}


	/** Handle a message from vscode */
	handleMessage(msg: Message) {
		switch(msg.type) {
			case MessageType.qedStatus:
				const statuses = msg.body as QedStatus[];  // one status for each input area, in order
				this.updateQedStatus(statuses);
				break;
			case MessageType.lineNumbers:
				this.setLineNumbers(msg.body);
				break;
			case MessageType.teacher:
				this.updateLockingState(msg.body);
				break;
			case MessageType.progress:
				const progressParams = msg.body as SimpleProgressParams;
				this.updateProgressBar(progressParams);
				break;
			case MessageType.diagnostics:
				const diagnostics = msg.body;
				this.parseCoqDiagnostics(diagnostics);
				break;
            case MessageType.syntax:
                initializeTacticCompletion(msg.body as boolean);
                break;
			default:
				// If we reach this 'default' case, then we have encountered an unknown message type.
				console.log(`[WEBVIEW] Unrecognized message type '${msg.type}'`);
				break;
		}
	}

	/**
	 * Wrapper around `this._api.postMessage(msg: Message)`
	 * @param message The message to post to the extension host
	 */
	post(message: Message): void {
		this._api.postMessage(message);
	}
}