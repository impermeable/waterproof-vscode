import React, { Suspense, lazy, useEffect, useState } from "react";

import { GoalAnswer, PpString } from "../../lib/types";
import { ErrorBrowser } from "../goals/ErrorBrowser";
import { Goals } from "../goals/Goals";
import { Hypothesis } from "./Hypothesis";

import "../styles/info.css";
import { Message, MessageType } from "../../shared";

// Dynamic import because the project uses CommonJS and the module is an ECMAScript module
// Top level await is supported with other `module` options in tsconfig.json
const VSCodeDivider = lazy(async () => {
  const { VSCodeDivider } = await import("@vscode/webview-ui-toolkit/react");
  return { default: VSCodeDivider };
});


export function Debug() {
  const [goals, setGoals] = useState<GoalAnswer<PpString>>();

  //handles the message
  //event : CoqMessageEvent as defined above
  function infoViewDispatch(msg: Message) {
    if (msg.type === MessageType.renderGoals) {
      // most important case that actually get the information
      setGoals(msg.body);
    }
  }

  // Set the callback, adds and removes the event listener
  useEffect(() => {
    const callback = (ev: MessageEvent<Message>) => {infoViewDispatch(ev.data);};
    window.addEventListener("message", callback);
    return () => window.removeEventListener("message", callback);
  }, []);

  if (!goals) {
    return <div>Place your cursor in the document to show the goals and hypothesis at that position.</div>
  }

  //the goals and hypothesis are displayed primarily
  //if an error occurs at the specified line this error will also be displayed
  //the following components are used: Hypothesis, Goals, ErrorBrowser
  return (
    <div className="info-panel-container">
      <div className="info-panel">
        <Hypothesis  goals={goals.goals} pos={goals.position} textDoc={goals.textDocument}/>
        <Goals goals={goals.goals} pos={goals.position} textDoc={goals.textDocument} />
      </div>

      {!goals.error ? null : (
        <div className="error-browser">
          <Suspense>
            <VSCodeDivider />
          </Suspense>
          <ErrorBrowser error={goals.error} />
        </div>
      )}
    </div>
  )
}

export default Debug;
