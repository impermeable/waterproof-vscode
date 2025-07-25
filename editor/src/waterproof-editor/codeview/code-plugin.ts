/*---------------------------------------------------------
 *  Adapted from https://github.com/benrbray/prosemirror-math/blob/master/src/math-plugin.ts
 *--------------------------------------------------------*/

// prosemirror imports
import { Schema, Node as ProseNode } from "prosemirror-model";
import { Plugin as ProsePlugin, PluginKey, PluginSpec } from "prosemirror-state";
import { EditorView } from "prosemirror-view";
import { CodeBlockView } from "./nodeview";
import { ReplaceStep } from "prosemirror-transform";
import { LineNumber } from "../../../../shared";

////////////////////////////////////////////////////////////

export interface ICodePluginState {
	macros: { [cmd:string] : string };
	/** A list of currently active `NodeView`s, in insertion order. */
	activeNodeViews: Set<CodeBlockView>; // I suspect this will break;
    /** The schema of the outer editor */
    schema: Schema;
    /** Should the codemirror cells show line numbers */
    showLines: boolean;
	/** The lastest versioned linenumbers */
	lines: LineNumber;
}

export const CODE_PLUGIN_KEY = new PluginKey<ICodePluginState>("waterproof-editor-code-plugin");

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
		const pluginState = CODE_PLUGIN_KEY.getState(view.state);
		if(!pluginState){ throw new Error("no codemirror code plugin!"); }
		const nodeViews = pluginState.activeNodeViews;

		// set up NodeView
		const nodeView = new CodeBlockView(node, view, getPos, pluginState.schema);

		nodeViews.add(nodeView);
		return nodeView;
	}
}


const CoqCodePluginSpec:PluginSpec<ICodePluginState> = {
	key: CODE_PLUGIN_KEY,
	state: {
		init(config, instance){
			return {
				macros: {},
				activeNodeViews: new Set<CodeBlockView>(),
                showLines: false,
                schema: instance.schema,
				lines: {linenumbers: [], version: 0},
			};
		},
		apply(tr, value, _oldState, _newState){
			// produce updated state field for this plugin
			let lineState = value.showLines;
			let newlines = value.lines;
			// Check if a node has been deleted
			if (tr.steps.length > 0) {
				for (const step of tr.steps) {
					if (step instanceof ReplaceStep && step.slice.content.firstChild === null) {
						for (const view of value.activeNodeViews) {
							// @ts-expect-error FIXME: Handle possible undefined view._getPos()
							if (view._getPos() === undefined || (view._getPos() >= step.from && view._getPos() < step.to)) value.activeNodeViews.delete(view);
						} 
					}
				}
			}

			// Update the state 
			const meta = tr.getMeta(CODE_PLUGIN_KEY);
			if (meta) {
				if (meta.setting === "update")
					lineState = meta.show;
				else 
					newlines = meta;
				
				if (value.activeNodeViews.size == newlines.linenumbers.length) {
					let i = 0;
					for (const view of value.activeNodeViews) {
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
			}
		}
	},
	props: {
		nodeViews: {
			"coqcode" : createCoqCodeView()
		}
	}
};

export const codePlugin = new ProsePlugin(CoqCodePluginSpec);


