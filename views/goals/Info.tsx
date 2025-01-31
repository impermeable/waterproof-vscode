import { Suspense, lazy, useEffect, useState } from "react";

import { GoalAnswer, PpString } from "../../lib/types";
import { CoqMessageEvent } from "../lib/CoqMessage";
import { ErrorBrowser } from "./ErrorBrowser";
import { Goals } from "./Goals";
import { Messages } from "./Messages";

import "../styles/info.css";
import { Message, MessageType } from "../../shared";

// Dynamic import because the project uses CommonJS and the module is an ECMAScript module
// Top level await is supported with other `module` options in tsconfig.json
const VSCodeDivider = lazy(async () => {
  const { VSCodeDivider } = await import("@vscode/webview-ui-toolkit/react");
  return { default: VSCodeDivider };
});


export function InfoPanel() {
  //saves the goal
  let [goals, setGoals] = useState<GoalAnswer<PpString>>();
  //boolean to check if the goals are still loading
  const [isLoading, setIsLoading] = useState(false);

  //handles the message
  function infoViewDispatch(msg: Message) { // TODO: make this change in logbook as well
    if (msg.type === MessageType.renderGoals) {
      const goals = msg.body.goals;
      
      // FIXME: The `renderGoals` message type is currently overloaded for very different functions.
      // This should be changed. 
      //@ts-ignore 
      setGoals(goals); //setting the information
      setIsLoading(false);
      
    }
  }

  // Set the callback
  useEffect(() => {
    const callback = (ev: MessageEvent) => {infoViewDispatch(ev.data as Message)};
    window.addEventListener("message", callback);
    return () => window.removeEventListener("message", callback);
  }, []);

  //show that the messages are loading
  if (isLoading) return <div>Loading...</div>;

  if (!goals) {
    return <div>Place your cursor in the document to show the goals at that position.</div>
  }

  //The goal and message are displayed along with the error at the position (if it exists)
  //Components used: Goals, Messages, ErrorBrowser
  return (
    <div className="info-panel-container">
      <div className="info-panel">
          <Goals goals={goals.goals} pos={goals.position} textDoc={goals.textDocument} />
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
    </div>
  );
}

export default InfoPanel;
