import { Suspense, lazy, useEffect, useState } from "react";

import { GoalAnswer, HypVisibility, PpString } from "../../lib/types";
import { ErrorBrowser } from "../goals/ErrorBrowser";
import { Goals } from "../goals/Goals";
import { Messages } from "../goals/Messages";


import "../styles/info.css";
import { Message, MessageType } from "../../shared";

// Dynamic import because the project uses CommonJS and the module is an ECMAScript module
// Top level await is supported with other `module` options in tsconfig.json
const VSCodeDivider = lazy(async () => {
  const { VSCodeDivider } = await import("@vscode/webview-ui-toolkit/react");
  return { default: VSCodeDivider };
});


export function Debug() {
  // visibility of the hypotheses in the goals panel
  
  //saves the goal
  const [goals, setGoals] = useState<GoalAnswer<PpString>>();
  //boolean to check if the goals are still loading
  const [isLoading, setIsLoading] = useState(false);

  //handles the message
  //event : CoqMessageEvent as defined above
  function infoViewDispatch(msg: Message) { 
    if (msg.type === MessageType.renderGoals) {
      const goals = msg.body.goals;

      setGoals(goals); //setting the information
      setIsLoading(false);
    }
  }

  // Set the callback
  useEffect(() => {
    const callback = (ev: MessageEvent<Message>) => {infoViewDispatch(ev.data);};
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
          <Goals goals={goals.goals} pos={goals.position} textDoc={goals.textDocument} visibility={HypVisibility.All}/>
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

export default Debug;

