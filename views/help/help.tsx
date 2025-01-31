import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import objectHash from "object-hash";
import React, { useEffect, useRef, useState } from "react";

import { Message, MessageType } from "../../shared";
import "../styles/execute.css";
import { Messages } from '../goals/Messages';

const date = new Date();
const vscode = acquireVsCodeApi();

export function Help() {
    // create the states for the components that need them
    const [isLoading, setIsLoading] = useState(false);
    const [info, setInfo] = useState([""]);

    //on changes in component useEffect is run
    useEffect(() => {
        //handling a message
        const handleMessage = (msg: Message) => {
            switch (msg.type){
                // insert message which is either a symbol or tactic
                case MessageType.insert:
                    break;
                // receiving info of the executed commands
                case MessageType.setData:
                    //@ts-ignore
                    setInfo(msg.body.data);
                    setIsLoading(false);
                    break;
            }
        };

        const callback = (ev: MessageEvent) => {handleMessage(ev.data as Message)};
        //adding event listener to component
        window.addEventListener('message', callback);

        return () => {
            // on dismount of component the eventlistener is removed
          window.removeEventListener('message', callback);
        };
      }, [ info ]);

    //button press help
    const handleHelp = () => {
        //Send the message indicating the help button was pressed
        vscode.postMessage({time: date.getTime(), type: MessageType.command, body: "Help."});
        setIsLoading(true);
    };
    return (
        <div className="info-panel-container">
            <div className="sentence">
                <table>
                    <tbody>
                        <tr>
                        <td>
                            <div className="sentence">
                                {/* help button */}
                                <VSCodeButton onClick={handleHelp}>Help</VSCodeButton>
                            </div>
                        </td>
                        <td></td>
                        <td></td>
                        </tr>
                    </tbody>
                </table>

            </div>
            {/* when loading show loading */}
            {isLoading ? (
            <div className="sentence">Loading...</div>
            ) : (
            <>
            {/* when done show results */}
            {info.length === 0 ? (
                <div>No results</div>
                ) : (
                    <>
                    {Array.isArray(info)  && info !== undefined && (
                   <React.Fragment>
                     {info[0]}
                     <VSCodeDivider />
                   </React.Fragment>
                 )}
                     {info !== undefined && !Array.isArray(info) &&(
                       <React.Fragment>
                         <Messages answer={info} />
                         <VSCodeDivider />
                       </React.Fragment>
                     )}
                   </>
            )}
      </>
    )}
        </div>
    );

}



export default Help;
