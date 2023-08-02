// Main panel components
import React from "react";
import "../goals/media/info.css";
// react components from the UI-toolkit
import { VSCodeButton, VSCodeCheckbox } from '@vscode/webview-ui-toolkit/react';

// First part, which should be split out is the protocol definition, second part is the UI.

/**
 * Here we add functions and interfaces
 */

export function Example() {

  return (
    <div className="info-panel-container">
      <div className="info-panel">
        <p>Here we use react!</p>
        <VSCodeButton>Example button</VSCodeButton>
        <VSCodeCheckbox/>
      </div>
    </div>
  );
}

export default Example;
