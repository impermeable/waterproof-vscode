// Importing necessary components from various packages
import { EditorState, Plugin, PluginKey, PluginSpec, Transaction } from "prosemirror-state";
import { CoqFileProgressKind, SimpleProgressParams } from "../../../shared";

// Interface for the state of the progress plugin
export interface IProgressPluginState {
  progressParams: SimpleProgressParams;
  totalProcessed: number;
  totalLines: number;
  resetProgressBar: boolean;
  currentLineNumbers: number[];
  processedLineSet: Set<number>;
}

// Plugin key for the progress plugin
export const PROGRESS_PLUGIN_KEY = new PluginKey<IProgressPluginState>("prosemirror-progressBar");

// Function to create a progress bar given the progress state and the container for the progress bar
function createProgressBar(progressState, progressBarContainer) {
  const { progressParams, totalProcessed, totalLines, resetProgressBar, currentLineNumbers } = progressState;

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
    
    // Create a new progress bar
    progressBar = document.createElement('progress');
    progressBarContainer.appendChild(progressBar);
  } else {
    // If resetProgressBar is false, we just update the existing progress bar
    progressBar = progressBarContainer.querySelector('progress');
  }
  
  // Set the properties of the progress bar
  if (progressBar) {
    progressBar.max = totalLines;

    if (progressParams.progress.length > 0) {
      progressBar.value = totalProcessed;
    } else {
      progressBar.value = totalLines;
    }
  }

  // Create a span for the text
  let progressBarText = document.createElement('span');
  progressBarText.className = 'progress-bar-text';

  // Create a string with all line numbers separated by commas
  let lineNumberString = currentLineNumbers.join(", ");
  
  // Set the text of the span
  if (currentLineNumbers.length > 0) {
    progressBarText.textContent = `Progress: ${Math.round((progressBar.value / progressBar.max) * 100)}%, Currently at lines: ${lineNumberString}`;
  } else {
    progressBarText.textContent = `Progress: ${Math.round((progressBar.value / progressBar.max) * 100)}%`;
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
        totalProcessed: 0,
        totalLines: 0,
        resetProgressBar: true,
        currentLineNumbers: [],
        processedLineSet: new Set<number>()
      };
    },
    apply(tr: Transaction, value: IProgressPluginState, oldState: EditorState, newState: EditorState): IProgressPluginState {
      // Retrieve progress parameters from the transaction meta data
      const progressParams: SimpleProgressParams = tr.getMeta(PROGRESS_PLUGIN_KEY);
      if (progressParams != null) {
        const resetProgressBar = (progressParams.numberOfLines !== value.totalLines);
    
        let currentLineNumbers: number[] = [];
    
        // If there are lines being processed, set currentLineNumbers to all of them
        if (progressParams.progress.length > 0) {
          currentLineNumbers = progressParams.progress.map(info => info.range.start.line);
        }

        let uniqueProcessedLines: Set<number>;

        // If resetProgressBar is true, reset the processedLineSet
        if (resetProgressBar) {
          uniqueProcessedLines = new Set<number>();
        } else {
          uniqueProcessedLines = value.processedLineSet;
        }

        let newLinesProcessed = 0;
        currentLineNumbers.forEach(lineNumber => {
          if (!uniqueProcessedLines.has(lineNumber)) {
            uniqueProcessedLines.add(lineNumber);
            newLinesProcessed++;
          }
        });
    
        return { 
          progressParams,
          totalProcessed: resetProgressBar ? newLinesProcessed : value.totalProcessed + newLinesProcessed,
          totalLines: progressParams.numberOfLines,
          resetProgressBar,
          currentLineNumbers,
          processedLineSet: uniqueProcessedLines
        };
      }
      return value;
    }
  },
  view(editorView) {
    // Create a container for the progress bar
    let progressBarContainer = document.createElement('div');
    progressBarContainer.className = 'progress-bar';

    // Insert the progress bar container into the DOM
    let parentNode = editorView.dom.parentNode;
    if (parentNode == null) {
      throw Error("editorView.dom.parentNode cannot be null here");
    }
    parentNode.insertBefore(progressBarContainer, editorView.dom);

    return {
      update(view, prevState) {
        // Update the progress bar with the current state
        let progressState = PROGRESS_PLUGIN_KEY.getState(view.state);
        if (progressState) {
          createProgressBar(progressState, progressBarContainer);
        }
      },
    };
  }
};

// Create a new instance of the progress bar plugin
export const progressBarPlugin = new Plugin(ProgressBarPluginSpec);
