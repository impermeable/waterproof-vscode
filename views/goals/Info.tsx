import React, { Suspense, lazy, useEffect, useState } from "react";
import { GoalAnswer, HypVisibility, PpString } from "../../lib/types";
import { ErrorBrowser } from "./ErrorBrowser";
import { Goals } from "./Goals";
import { Messages } from "./Messages";
import {Help} from "./help";

import "../styles/info.css";
import { Message, MessageType } from "../../shared";

import vscode from "./vscode";

// Dynamic import because the project uses CommonJS and the module is an ECMAScript module
// Top level await is supported with other `module` options in tsconfig.json
const VSCodeDivider = lazy(async () => {
  //@ts-expect-error This module does exist but we have no type for the react part
  const { VSCodeDivider } = await import("@vscode/webview-ui-toolkit/react");
  return { default: VSCodeDivider };
});
 
export function InfoPanel() {
  // visibility of the hypotheses in the goals panel
  
  //saves the goal
  const [goals, setGoals] = useState<GoalAnswer<PpString>>();
  //boolean to check if the goals are still loading
  const [goalsLoading, setGoalsLoading] = useState(false);
  //visibility of the hypotheses in the goals panel as State
  const [visibility, setVisibility] = useState<HypVisibility>(HypVisibility.None);
  
  const [isHelpLoading, setHelpIsLoading] = useState(false);
  const [helpInfo, setHelpInfo] = useState([""]);
  //handles the message
  //event : CoqMessageEvent as defined above
  function infoViewDispatch(msg: Message) { 
    switch (msg.type) {
      case MessageType.renderGoals:
          setGoals(msg.body.goals); //setting the information
          setGoalsLoading(false);
          setVisibility(msg.body.visibility ?? HypVisibility.None); //set visibility if it exists, otherwise set to None  
          break;
      case MessageType.setData:
        //@ts-expect-error FIXME: setInfo expects string[]
        // in theory setData can also contain GoalAnswer
        setHelpInfo(msg.body);
        setHelpIsLoading(false);
        break;
    }
  }

  // Set the callback
  useEffect(() => {
    const callback = (ev: MessageEvent<Message>) => {infoViewDispatch(ev.data);};
    window.addEventListener("message", callback);
    return () => window.removeEventListener("message", callback);
  }, []);

  const requestHelp = () => {
    setHelpIsLoading(true);
    vscode.postMessage({
      type: MessageType.command,
      body: { command: "Help.", time: Date.now() },
    });
  };

  //show that the messages are loading
  if (goalsLoading) return <div>Loading...</div>;

  if (!goals) {
    return <div>Place your cursor in the document to show the goals at that position.</div>
  }

  //The goal and message are displayed along with the error at the position (if it exists)
  //Components used: Goals, Messages, ErrorBrowser, Help button.
  return (
    <div className="info-panel-container">
      <div className="info-panel">
          <Goals goals={goals.goals} pos={goals.position} textDoc={goals.textDocument} visibility={visibility}/>
          <Messages answer={goals} />
      </div>
      {!goals.error ? null : (
        <div className="error-browser">
          <Suspense>
            <VSCodeDivider />
          </Suspense>
          <ErrorBrowser error={goals.error} />
        </div>
      )}
      <div className="help-panel">
          <Help helpInfo ={helpInfo} isLoading={isHelpLoading} onRequestHelp={requestHelp}/>
      </div>
    </div>
  );
}

export default InfoPanel;
