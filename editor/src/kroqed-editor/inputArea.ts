import { EditorState, Plugin, PluginKey, PluginSpec, Transaction } from 
"prosemirror-state";

/**
 * Interface describing the state of the input are plugin.
 * Contains fields `locked: boolean` indicating wether non-input areas should be locked (ie. non-teacher mode) and
 * `globalLock: boolean` indicating that we are in a global lockdown state (caused by an unrecoverable error).
 */
export interface IInputAreaPluginState {
	teacher: boolean;
    globalLock: boolean;
}

/** The plugin key for the input area plugin */
export const INPUT_AREA_PLUGIN_KEY = new PluginKey<IInputAreaPluginState>("prosemirror-locking");

// The plugin spec describing this plugin.
const InputAreaPluginSpec : PluginSpec<IInputAreaPluginState> = {
    // Assign the plugin key.
	key: INPUT_AREA_PLUGIN_KEY,
	state: {
		init(_config, _instance){
            // Initially set the locked state to true and globalLock to false.
			return {
                teacher: false,
                globalLock: false,
			};
		},
		apply(tr : Transaction, value: IInputAreaPluginState, _oldState: 
            EditorState, _newState: EditorState
        ){
			// produce updated state field for this plugin
            
            const meta = tr.getMeta(INPUT_AREA_PLUGIN_KEY);
            if (meta === undefined) {
                return value;
            } else {
                let newGlobalLock = value.globalLock;
                let newTeacher = value.teacher;
                if (meta == "ErrorMode") {
                    // We are in a global locked state if we receive this meta.
                    newTeacher = value.teacher;
                    newGlobalLock = true;

                    // If we are in lockdown then we remove the editor and show an error message.
                    const node = document.querySelector("#editor");
                    if (!node) throw new Error("Node cannot be undefined here");
                    node.innerHTML = "";
                    const container = document.createElement("div");
                    container.classList.add("frozen-thingie");
                    container.innerHTML = `<div class="frozen-emoji">💀</div><div class="frozen-message">DOCUMENT FROZEN!<br>Reopen file...</div>`;
                    node.appendChild(container);
                } else {
                    newTeacher = meta.teacher ?? false;
                }
                return {
                    teacher: newTeacher,
                    globalLock: newGlobalLock,
                };
            }
		}
	},
	props: {
        editable: (state) => {
            // Get locked and globalLock states from the plugin.
            const teacher = INPUT_AREA_PLUGIN_KEY.getState(state)?.teacher ?? false;
            const globalLock = INPUT_AREA_PLUGIN_KEY.getState(state)?.globalLock ?? false;
            
            // In the `globalLock` state nothing is editable anymore.
            if (globalLock) return false;
            
            // In teacher mode, everything is editable by default.
            if (teacher) return true;

            // Get the from selection component.
            const { $from } = state.selection;

            // Assume non-editable.
            let isEditable = false;

            // Check if the current selection is inside an input area.
            state.doc.nodesBetween($from.pos, $from.pos, (node) => {
                if (node.type.name === "input") {
                    // If so, this cell is editable.
                    isEditable = true;
                }
            });

            // Return editable state.
            return isEditable;
        }
    }
};

// Export the input area plugin for use in the editor.
export const inputAreaPlugin = new Plugin(InputAreaPluginSpec);