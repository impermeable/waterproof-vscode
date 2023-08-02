/*---------------------------------------------------------
 *  Adapted from https://github.com/benrbray/prosemirror-math/blob/master/src/math-plugin.ts
 *--------------------------------------------------------*/

// prosemirror imports
import { Schema, Node as ProseNode } from "prosemirror-model";
import { Plugin as ProsePlugin, PluginKey, PluginSpec, TextSelection } from "prosemirror-state";
import { EditorView } from "prosemirror-view";
import { MarkdownView } from "./MarkdownView";

////////////////////////////////////////////////////////////

export interface IRealMarkdownPluginState {
	macros: { [cmd:string] : string };
	/** A list of currently active `NodeView`s, in insertion order. */
	activeNodeViews: MarkdownView[];
	/** The selection of the current cursor position */
	cursor: TextSelection | undefined;
	/** Last cursor position in view, so that it can be displayed */
}

export const REAL_MARKDOWN_PLUGIN_KEY = new PluginKey<IRealMarkdownPluginState>("prosemirror-realtime-markdown");

/** 
 * Returns a function suitable for passing as a field in `EditorProps.nodeViews`.
 * @see https://prosemirror.net/docs/ref/#view.EditorProps.nodeViews
 */
export function createRealMarkdownView(schema: Schema){
	return (node: ProseNode, view: EditorView, getPos: (() => number | undefined)): MarkdownView => {
		/** @todo is this necessary?
		* Docs says that for any function proprs, the current plugin instance
		* will be bound to `this`.  However, the typings don't reflect this.
		*/
		let pluginState = REAL_MARKDOWN_PLUGIN_KEY.getState(view.state);
		if(!pluginState){ throw new Error("no realtime markdown plugin!"); }
		let nodeViews = pluginState.activeNodeViews;

		// set up NodeView
		let nodeView = new MarkdownView(getPos, view, node.textContent, node, schema, REAL_MARKDOWN_PLUGIN_KEY, "markdown");

		nodeViews.push(nodeView);
		return nodeView;
	}
}


const RealMarkdownPluginSpec = (schema: Schema): PluginSpec<IRealMarkdownPluginState> => { 
	return {
		key: REAL_MARKDOWN_PLUGIN_KEY,
		state: {
			init(config, instance){
				return {
					cursor: undefined,
					macros: {},
					activeNodeViews: []
				};
			},
			apply(tr, value, oldState, newState){
				// produce updated state field for this plugin
				let newCur = value.cursor;
				if(tr.getMeta(REAL_MARKDOWN_PLUGIN_KEY)) newCur = tr.getMeta(REAL_MARKDOWN_PLUGIN_KEY);
				// If the transaction has a new TextSelection, ensure this cursor is not set so it does not override
				if(tr.selectionSet && tr.selection instanceof TextSelection) newCur = undefined;
				return {
					// these values are left unchanged
					activeNodeViews : value.activeNodeViews,
					macros          : value.macros,
					cursor          : newCur
				}
			}
		},
		props: {
			nodeViews: {
				"markdown" : createRealMarkdownView(schema)
			}
		}
	};
}
export const realMarkdownPlugin = (schema: Schema) => new ProsePlugin(RealMarkdownPluginSpec(schema));