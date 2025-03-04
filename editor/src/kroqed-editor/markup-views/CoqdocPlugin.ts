/*---------------------------------------------------------
 *  Adapted from https://github.com/benrbray/prosemirror-math/blob/master/src/math-plugin.ts
 *--------------------------------------------------------*/

// prosemirror imports
import { Schema, Node as ProseNode } from "prosemirror-model";
import { Plugin as ProsePlugin, PluginKey, PluginSpec } from "prosemirror-state";
import { EditorView } from "prosemirror-view";
import { CoqdocView } from "./CoqdocView";

////////////////////////////////////////////////////////////

export interface ICoqdocPluginState {
	macros: { [cmd:string] : string };
	/** A list of currently active `NodeView`s, in insertion order. */
	activeNodeViews: CoqdocView[];
}

export const COQDOC_PLUGIN_KEY = new PluginKey<ICoqdocPluginState>("prosemirror-coqdoc-rendering");

/** 
 * Returns a function suitable for passing as a field in `EditorProps.nodeViews`.
 * @see https://prosemirror.net/docs/ref/#view.EditorProps.nodeViews
 */
export function createCoqdocView(schema: Schema){
	return (node: ProseNode, view: EditorView, getPos: () => number | undefined): CoqdocView => {
		/** @todo is this necessary?
		* Docs says that for any function proprs, the current plugin instance
		* will be bound to `this`.  However, the typings don't reflect this.
		*/
		const pluginState = COQDOC_PLUGIN_KEY.getState(view.state);
		if(!pluginState){ throw new Error("no coqdoc plugin!"); }
		const nodeViews = pluginState.activeNodeViews;

		// set up NodeView
		const nodeView = new CoqdocView(getPos, view, node.textContent, node, schema, COQDOC_PLUGIN_KEY, "coqdoc");
		nodeViews.push(nodeView);
		return nodeView;
	}
}

const coqdocPluginSpec = (schema: Schema):PluginSpec<ICoqdocPluginState> => {
	return {
		key: COQDOC_PLUGIN_KEY,
		state: {
			init(_config, _instance){
				return {
					macros: {},
					activeNodeViews: []
				};
			},
			apply(tr, value, _oldState, _newState){
				// produce updated state field for this plugin
				return {
					// these values are left unchanged
					activeNodeViews : value.activeNodeViews,
					macros          : value.macros
				}
			}
		},
		props: {
			nodeViews: {
				"coqdown" : createCoqdocView(schema)
			}
		}
	}
};

export const coqdocPlugin = (schema: Schema) => new ProsePlugin(coqdocPluginSpec(schema));