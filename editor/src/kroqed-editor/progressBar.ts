// Importing necessary components from various packages
import { EditorState, Plugin, PluginKey, PluginSpec, Transaction } from "prosemirror-state";
import { SimpleProgressParams } from "../../../shared";

// Interface for the state of the progress plugin
export interface IProgressPluginState {
  progressParams: SimpleProgressParams;
  resetProgressBar: boolean;
  endLine: number;
  startLine: number;
}

// Plugin key for the progress plugin
export const PROGRESS_PLUGIN_KEY = new PluginKey<IProgressPluginState>("prosemirror-progressBar");

function startSpinner(spinnerContainer) {
  spinnerContainer.classList.add('spinner');
}

function stopSpinner(spinnerContainer) {
  spinnerContainer.classList.remove('spinner');
}

// Function to create a progress bar given the progress state and the container for the progress bar
function createProgressBar(progressState, progressBarContainer, spinnerContainer) {
  const { progressParams, resetProgressBar, endLine, startLine } = progressState;

  // Remove existing progress bar text
  let oldProgressBarText = progressBarContainer.querySelector('.progress-bar-text');
  if (oldProgressBarText) {
    progressBarContainer.removeChild(oldProgressBarText);
  }

  let progressBar;
  
  if (resetProgressBar) {
    // If resetProgressBar is true, remove existing progress element
    let oldProgress = progressBarContainer.querySelector('progress');
    if (oldProgress) {
      progressBarContainer.removeChild(oldProgress);
    }
  } else {
    // If resetProgressBar is false, we just update the existing progress bar
    progressBar = progressBarContainer.querySelector('progress');
  }
  
  if (progressBar == null) {
    progressBar = document.createElement('progress');
    progressBarContainer.appendChild(progressBar);
  }

  // Set the properties of the progress bar
  progressBar.max = endLine;

  if (progressParams.progress.length > 0) {
    progressBar.value = startLine;
  } else {
    progressBar.value = endLine;
  }

  // Create a span for the text
  let progressBarText = document.createElement('span');
  progressBarText.className = 'progress-bar-text';

  
  // Set the text of the span
  if (progressParams.progress.length > 0) {
    progressBarText.textContent = `Verifying file, currently at line: ${startLine + 1}`;
  } else {
    progressBarText.textContent = `File verified`;
  }

  progressBarContainer.appendChild(progressBarText);
}

// Spec for the progress bar plugin
let ProgressBarPluginSpec: PluginSpec<IProgressPluginState> = {
  key: PROGRESS_PLUGIN_KEY,
  state: {
    init(config, instance) {
      return {
        progressParams: {
          numberOfLines: 1,
          progress: []
        },
        resetProgressBar: true,
        endLine: 1,
        startLine: 1,
      };
    },
    apply(tr: Transaction, value: IProgressPluginState, oldState: EditorState, newState: EditorState): IProgressPluginState {
      // Retrieve progress parameters from the transaction meta data
      const progressParams: SimpleProgressParams = tr.getMeta(PROGRESS_PLUGIN_KEY);
      if (progressParams != null) {
        // If lines are being progressed, we reset the progress bar
        const resetProgressBar = (progressParams.progress.length > 0);
        return { 
          progressParams,
          resetProgressBar,
          startLine: resetProgressBar ? progressParams.progress[0].range.start.line + 1 : 1,
          endLine: resetProgressBar ? progressParams.progress[0].range.end.line + 1 : 1,
        };
      }
      return value;
    }
  },
  view(editorView) {
    // Create a container for the progress bar
    let progressBarContainer = document.createElement('div');
    progressBarContainer.className = 'progress-bar';
    let spinnerContainer = document.createElement('div');
    spinnerContainer.className = 'spinner-container';

    // Insert the progress bar container into the DOM
    let parentNode = editorView.dom.parentNode;
    if (parentNode == null) {
      throw Error("editorView.dom.parentNode cannot be null here");
    }
    parentNode.insertBefore(progressBarContainer, editorView.dom);
    parentNode.insertBefore(spinnerContainer, editorView.dom);

    return {
      update(view, prevState) {
        // Update the progress bar with the current state
        let progressState = PROGRESS_PLUGIN_KEY.getState(view.state);
        if (progressState) {
          createProgressBar(progressState, progressBarContainer, spinnerContainer);
        }
      },
    };
  }
};

// Create a new instance of the progress bar plugin
export const progressBarPlugin = new Plugin(ProgressBarPluginSpec);
