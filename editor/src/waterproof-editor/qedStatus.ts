// Importing necessary modules from prosemirror-state and prosemirror-view
import { EditorState, Plugin, PluginKey, PluginSpec } from 'prosemirror-state';
import { Decoration, DecorationSet } from 'prosemirror-view';
import { findDescendantsWithType } from './utilities';
import { InputAreaStatus } from '../../../shared';
import { WaterproofEditor } from './editor';

// Define interface for UpdateStatusPluginState
export interface IUpdateStatusPluginState {
  status: InputAreaStatus[];
}

// Key to identify the plugin within ProseMirror's plugin system
export const UPDATE_STATUS_PLUGIN_KEY = new PluginKey<IUpdateStatusPluginState>('prosemirror-status-update');

// Helper function to convert status updates to appropriate CSS classes
const statusToDecoration = (status: InputAreaStatus) => {
  switch (status) {
    case InputAreaStatus.Proven:
      return 'proven';
    case InputAreaStatus.Incomplete:
      return 'incomplete';
    case InputAreaStatus.Invalid:
      return '';
  }
};

// Plugin specification
const UpdateStatusPluginSpec = (editor: WaterproofEditor): PluginSpec<IUpdateStatusPluginState> => {
  return {
    key: UPDATE_STATUS_PLUGIN_KEY,
    state: {
      // The function to initialize the plugin state
      init(_config, _instance){
        return {
          status: [],
        };
      },
      // Function to apply updates to the plugin state
      apply(tr, value, _oldState, _newState){
        const newStatus = tr.getMeta(UPDATE_STATUS_PLUGIN_KEY);
        if (newStatus === undefined) {
          return value;
        } else {
          return {
            status: newStatus,
          };
        }
      }
    },
    props: {
      // Function to compute decorations based on the plugin state
      decorations: (state: EditorState) => {
        const statusUpdate = UPDATE_STATUS_PLUGIN_KEY.getState(state)?.status;
        if (statusUpdate && statusUpdate.length > 0) {
          // Get all input nodes in the document
          const inputNodeType = state.schema.nodes.input;
          const inputNodes = findDescendantsWithType(state.doc, true, inputNodeType);

          if (!inputNodes || statusUpdate.length !== inputNodes.length) return null;

          const decorations: Decoration[] = [];
          inputNodes.forEach((inputNode, index) => {
            if (statusUpdate[index] !== undefined) {
              const newStatusUpdate = statusUpdate[index];
              if (inputNode.node.attrs.status !== newStatusUpdate) {
                // This is (probably) the place where we check for errors in the proof.
                // A proof should not be accepted if it includes a faulty coq statement.

                const start = inputNode.pos;
                const end = start + inputNode.node.nodeSize;
                const thingies = editor.getDiagnosticsInRange(start, end, 1);
                let className = statusToDecoration(newStatusUpdate);
                if (thingies.length > 0) {
                  if (thingies.find((value) => value.severity == 0)) {
                    // Coq error in proof.
                    className += "-contains-error";
                  } else {
                    className += "-contains-warning";
                  }
                }

                const decoration = Decoration.node(start, end, {
                  class: className,
                });
                decorations.push(decoration);
              }
            }
          });

          return DecorationSet.create(state.doc, decorations);
        }
        return null;
      },
    },
  };
}

// Create a new instance of the plugin
export const updateStatusPlugin = (editor: WaterproofEditor) => { return new Plugin(UpdateStatusPluginSpec(editor)) };
