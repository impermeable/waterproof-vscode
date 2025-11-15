import React, { Suspense, lazy, useEffect, useState } from "react";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import { GoalAnswer, HypVisibility, PpString } from "../../lib/types";
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

const date = new Date();
const vscode = acquireVsCodeApi();

export function InfoPanel() {
  // visibility of the hypotheses in the goals panel
  
  //saves the goal
  const [goals, setGoals] = useState<GoalAnswer<PpString>>();
  //boolean to check if the goals are still loading
  const [goalsLoading, setGoalsLoading] = useState(false);
  //visibility of the hypotheses in the goals panel as State
  const [visibility, setVisibility] = useState<HypVisibility>(HypVisibility.None);

  const [helpLoading, setHelpLoading] = useState(false);
  const [helpInfo, setHelpInfo] = useState([""]);

  
  //handles the message
  //event : CoqMessageEvent as defined above
  function infoViewDispatch(msg: Message) { 
    if (msg.type === MessageType.renderGoals) {
      const goals = msg.body.goals;

      setGoals(goals); //setting the information
      setGoalsLoading(false);
      setVisibility(msg.body.visibility ?? HypVisibility.None); //set visibility if it exists, otherwise set to None
    }
  }

  // Set the callback
  useEffect(() => {
    const callback = (ev: MessageEvent<Message>) => {infoViewDispatch(ev.data);};
    window.addEventListener("message", callback);
    return () => window.removeEventListener("message", callback);
  }, []);

  //on changes in component useEffect is run
  useEffect(() => {
    //handling a message
    const handleMessage = (msg: Message) => {
      if (msg.type === MessageType.setData) {
        //@ts-expect-error FIXME: setInfo expects string[]
        // in theory setData can also contain GoalAnswer
        setInfo(msg.body);
        setHelpLoading(false);
      }
    };
    const callback = (ev: MessageEvent<Message>) => {handleMessage(ev.data);};

    //adding event listener to component
    window.addEventListener('message', callback);

    return () => {
        // on dismount of component the eventlistener is removed
        window.removeEventListener('message', callback);
    };
  }, [ helpInfo ]);

  //show that the messages are loading
  if (goalsLoading) return <div>Loading...</div>;

  if (!goals) {
    return <div>Place your cursor in the document to show the goals at that position.</div>
  }
  const handleHelp = () => {
    //Send the message indicating the help button was pressed
    const msg: Message = { type: MessageType.command, body: {command: "Help.", time: date.getTime()} };
    vscode.postMessage(msg);
    setGoalsLoading(true);
  };
  //The goal and message are displayed along with the error at the position (if it exists)
  //Components used: Goals, Messages, ErrorBrowser, Help button.
  return (
    <div style={{ display: "flex", flexDirection: "column", height: "100vh" }}>
      <div style={{ flex: "1 1 50%", minHeight: 0, overflow: "auto" }}>
        <div className="info-panel-container">
          <div className="info-panel">
            <Goals
              goals={goals.goals}
              pos={goals.position}
              textDoc={goals.textDocument}
              visibility={visibility}
            />
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
      </div>

      <div
        style={{
          flex: "1 1 50%",
          minHeight: 0,
          overflow: "auto",
          borderTop: "1px solid var(--vscode-panel-border, #ddd)",
        }}
      >
        <div className="info-panel-container">
          <div className="sentence">
            <table>
              <tbody>
                <tr>
                  <td>
                    <div className="sentence">
                      <VSCodeButton onClick={handleHelp}>Help</VSCodeButton>
                    </div>
                  </td>
                  <td></td>
                  <td></td>
                </tr>
              </tbody>
            </table>
          </div>

          {helpLoading ? (
            <div className="sentence">Loading...</div>
          ) : helpInfo.length === 0 ? (
            <div>No results</div>
          ) : (
            <>
              {Array.isArray(helpInfo) ? (
                <>
                  {helpInfo[0]}
                  <Suspense>
                    <VSCodeDivider />
                  </Suspense>
                </>
              ) : (
                <>
                  <Messages answer={helpInfo} />
                  <Suspense>
                    <VSCodeDivider />
                  </Suspense>
                </>
              )}
            </>
          )}
        </div>
      </div>
    </div>
  );
}

export default InfoPanel;
