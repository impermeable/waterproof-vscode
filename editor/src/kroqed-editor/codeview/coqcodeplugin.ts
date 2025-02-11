/*---------------------------------------------------------
 *  Adapted from https://github.com/benrbray/prosemirror-math/blob/master/src/math-plugin.ts
 *--------------------------------------------------------*/

// prosemirror imports
import { Schema, Node as ProseNode, ResolvedPos } from "prosemirror-model";
import { Plugin as ProsePlugin, PluginKey, PluginSpec } from "prosemirror-state";
import { EditorView } from "prosemirror-view";
import { CodeBlockView } from "./nodeview";
import { ReplaceStep } from "prosemirror-transform";
import { LineNumber } from "../../../../shared";
import { DiagnosticSeverity } from "vscode";

////////////////////////////////////////////////////////////

/** Type that contains a coq diagnostics object fit for use in the ProseMirror editor context. */
type DiagnosticObjectProse = {message: string, start: number, end: number, $start: ResolvedPos, $end: ResolvedPos, severity: number};


export interface ICoqCodePluginState {
	macros: { [cmd:string] : string };
	/** A list of currently active `NodeView`s, in insertion order. */
	activeNodeViews: Set<CodeBlockView>; // I suspect this will break;
    /** The schema of the outer editor */
    schema: Schema;
    /** Should the codemirror cells show line numbers */
    showLines: boolean;
	/** The lastest versioned linenumbers */
	lines: LineNumber;
	/**  */
	diagnostics: DiagnosticObjectProse[];
}

export const COQ_CODE_PLUGIN_KEY = new PluginKey<ICoqCodePluginState>("prosemirror-coq-code");

/**
 * Returns a function suitable for passing as a field in `EditorProps.nodeViews`.
 * @see https://prosemirror.net/docs/ref/#view.EditorProps.nodeViews
 */
export function createCoqCodeView(){
	return (node: ProseNode, view: EditorView, getPos: () => number | undefined): CodeBlockView => {
		/** @todo is this necessary?
		* Docs says that for any function proprs, the current plugin instance
		* will be bound to `this`.  However, the typings don't reflect this.
		*/
		let pluginState = COQ_CODE_PLUGIN_KEY.getState(view.state);
		if(!pluginState){ throw new Error("no codemirror code plugin!"); }
		let nodeViews = pluginState.activeNodeViews;

		// set up NodeView
		let nodeView = new CodeBlockView(node, view, getPos, pluginState.schema);

		nodeViews.add(nodeView);
		return nodeView;
	}
}


let CoqCodePluginSpec:PluginSpec<ICoqCodePluginState> = {
	key: COQ_CODE_PLUGIN_KEY,
	state: {
		init(config, instance){
			return {
				macros: {},
				activeNodeViews: new Set<CodeBlockView>(),
                showLines: false,
                schema: instance.schema,
				lines: {linenumbers: [], version: 0},
				diagnostics: [],
			};
		},
		apply(tr, value, oldState, newState){
			// produce updated state field for this plugin
			let lineState = value.showLines;
			let newlines = value.lines;
			let diagnostics = value.diagnostics;
			// Check if a node has been deleted
			if (tr.steps.length > 0) {
				for (let step of tr.steps) {
					if (step instanceof ReplaceStep && step.slice.content.firstChild === null) {
						for (let view of value.activeNodeViews) {
							//@ts-ignore
							if (view._getPos() === undefined || (view._getPos() >= step.from && view._getPos() < step.to)) value.activeNodeViews.delete(view);
						}
					}
				}
			}

			// Update the state
			if (tr.getMeta(COQ_CODE_PLUGIN_KEY)) {
				if (tr.getMeta(COQ_CODE_PLUGIN_KEY) === "toggleLines") lineState = !lineState;
				else if (tr.getMeta(COQ_CODE_PLUGIN_KEY).length !== undefined) {
					const meta = tr.getMeta(COQ_CODE_PLUGIN_KEY);
					console.log("Setting diagnostics", meta);
					diagnostics = meta;
					for (const view of value.activeNodeViews) {
						view.updateDiagnostics();
					}
				}
				else newlines = tr.getMeta(COQ_CODE_PLUGIN_KEY);
				if (value.activeNodeViews.size == newlines.linenumbers.length) {
					let i = 0;
					for (let view of value.activeNodeViews) {
						view.updateLineNumbers(newlines.linenumbers[i] + 1, lineState);
						i++;
					}
				}
			}
			return {
				// these values are left unchanged
				activeNodeViews : value.activeNodeViews,
				macros          : value.macros,
                schema          : value.schema,
                showLines       : lineState,
				lines           : newlines,
				diagnostics
			}
		}
	},
	props: {
		nodeViews: {
			"coqcode" : createCoqCodeView()
		}
	}
};

export const coqCodePlugin = new ProsePlugin(CoqCodePluginSpec);


