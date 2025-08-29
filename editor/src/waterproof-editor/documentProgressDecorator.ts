import { Plugin, PluginKey, PluginSpec } from 'prosemirror-state';

// Interface for the document progress decorator plugin state
export interface IDocumentProgressDecoratorState {
  total: number;
  progressHeightLow: number;
  progressHeightHigh: number;
}

// Plugin key for the document progress decorator plugin
export const DOCUMENT_PROGRESS_DECORATOR_KEY = new PluginKey<IDocumentProgressDecoratorState>('prosemirror-document-progress-decorator');

// Spec for the document progress decorator plugin
const DocumentProgressDecoratorPluginSpec: PluginSpec<IDocumentProgressDecoratorState> = {
  key: DOCUMENT_PROGRESS_DECORATOR_KEY,
  state: {
    init(_config, _instance) {
      return {
        progressHeightLow: 0,
        progressHeightHigh: 0,
        total: 0
      };
    },
    apply(tr, value, _oldState, _newState) {
        const meta = tr.getMeta(DOCUMENT_PROGRESS_DECORATOR_KEY);
        return meta ?? value;
    }
  },
  view(editorView) {
    // Create the document progress decorator container
    const decoratorContainer = document.createElement('div');
    decoratorContainer.className = 'document-progress-decorator';

    // Insert the decorator container into the DOM
    const parentNode = editorView.dom.parentNode;
    if (parentNode == null) {
      throw Error("editorView.dom.parentNode cannot be null here");
    }
    
    // Position the decorator relative to the editor
    parentNode.insertBefore(decoratorContainer, editorView.dom);

    // Function to update the decorator height based on progress
    const updateDecorator = (state: IDocumentProgressDecoratorState) => {
        decoratorContainer.style.background = `linear-gradient(to bottom, #FFD700 0px, #ffd700 ${state.progressHeightLow}px, #ffe96dff ${state.progressHeightHigh}px, #ffffff ${state.progressHeightHigh + 1}px)`;
        decoratorContainer.style.height = `${state.total}px`;
    };

    // Initialize with current state
    const initialState = DOCUMENT_PROGRESS_DECORATOR_KEY.getState(editorView.state);
    if (initialState) {
      updateDecorator(initialState);
    }

    return {
      update(view, _prevState) {
        // Update the decorator based on current progress state
        const currentState = DOCUMENT_PROGRESS_DECORATOR_KEY.getState(view.state);
        if (currentState) {
          updateDecorator(currentState);
        }
      },
      destroy() {
        // Clean up the decorator when the plugin is destroyed
        if (decoratorContainer.parentNode) {
          decoratorContainer.parentNode.removeChild(decoratorContainer);
        }
      }
    };
  }
};

// Create a new instance of the document progress decorator plugin
export const documentProgressDecoratorPlugin = new Plugin(DocumentProgressDecoratorPluginSpec);
