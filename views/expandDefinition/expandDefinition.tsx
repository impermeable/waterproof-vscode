import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React, { useEffect, useRef, useState } from "react";

import { Message, MessageType } from "../../shared";
import "../styles/execute.css";
import { Messages } from '../goals/Messages';

const date = new Date();
const vscode = acquireVsCodeApi();

export function ExpandDefinition() {
    // create the states for the components that need them
    const [inputText1, setInputText1] = useState("");
    const [cursor1, setCursor1] = useState(0)
    const [inputText2, setInputText2] = useState("");
    const [cursor2, setCursor2] = useState(0)
    const [info, setInfo] = useState([""]);
    const [current, setCurrent] = useState("");
    const [isLoading, setIsLoading] = useState(false);

    const input1Ref = useRef(null);
    const input2Ref = useRef(null);

    //on changes in component useEffect is run
    useEffect(() => {
        //handling a message
        const handleMessage = (msg: Message) => {
            switch (msg.type){
                // insert message which is either a symbol or tactic
                case MessageType.insert:
                    insertText(msg.body.symbolUnicode);
                    break;
                // receiving info of the executed commands
                case MessageType.setData:
                    //@ts-expect-error
                    setInfo(msg.body);
                    setIsLoading(false);
                    break;
            }
        };

        const callback = (ev: MessageEvent<Message>) => {handleMessage(ev.data);};

        //adding event listener to component
        window.addEventListener('message', callback);

        return () => {
            // on dismount of component the eventlistener is removed
          window.removeEventListener('message', callback);
        };
      }, [ cursor1, cursor2, inputText1, inputText2, current, info ]);

      // the cursor position is updated together with the current textarea
      const setCursorPos = (textarea, cur) => {
        setCurrent(cur);
        if (textarea) {
            const startPos = textarea.selectionStart;
            const val = textarea.value;
            switch (cur) {
                // first input area of expand def in context
                case "input1":
                    setCursor1(startPos);
                    setInputText1(val);
                    break;
                // second input area of expand def in context
                case "input2":
                    setCursor2(startPos);
                    setInputText2(val);
                    break;
            }
        }
    }

    //inserting text at the previous cursor position
    const insertText = (textToInsert: string) => {
        let textarea = null;
        let cursor = 0;
        let value = "";
        switch (current) {
            // first input area of expand def in context
            case "input1":
                textarea = input1Ref.current;
                cursor = cursor1;
                value = inputText1;
                break;
            // second input area of expand def in context
            case "input2":
                textarea = input2Ref.current;
                cursor = cursor2;
                value = inputText2;
                break;
            default:
                break;
        }
        if (textarea) {
            const newValue = value.substring(0, cursor) +textToInsert +value.substring(cursor, value.length);
            (textarea as HTMLTextAreaElement).value = newValue;
            (textarea as HTMLTextAreaElement).setSelectionRange(cursor+textToInsert.length, cursor+textToInsert.length);
            (textarea as HTMLTextAreaElement).focus();
            //handles the insertion in the current text area
            switch (current) {
                // first input area of expand def in context
                case "input1":
                    setInputText1(newValue);
                    setCursor1(cursor +textToInsert.length);
                    break;
                // first input area of expand def in context
                case "input2":
                    setInputText2(newValue);
                    setCursor2(cursor +textToInsert.length);
                    break;
            }
        }
    };

    //button press execute
    const handleExecute = () => {
        //Send the message the execute button was pressed
        vscode.postMessage({time: date.getTime(), 
                            type: MessageType.command, 
                            body: `_internal_ Expand the definition of ${inputText1} in (${inputText2.replace(/(\.\s*|\s*)$/s, '')}).`})
        setIsLoading(true);
    };

    //execute by pressing search + enter in the first input field
    const handleKeyDown = (event) => {
        if (event.key === 'Enter' && event.shiftKey) {
            // Prevents adding a new line in the textarea
            event.preventDefault();
        }
        setCursorPos(input1Ref.current, "input1");
    };

    //execute by pressing search + enter in the second input field
    const handleKeyDown2 = (event) => {
        if (event.key === 'Enter' && event.shiftKey) {
            // Handle Shift + Enter key press logic here
            // Prevent adding a new line in the textarea
            event.preventDefault(); 
        }
    };

    //handle change in the first input of execute
    const handleChange = (_event) => {
        setCursorPos(input1Ref.current, "input1");
    };

    //handle change in the second input of execute
    const handleChange2 = (_event) => {
        setCursorPos(input2Ref.current, "input2");
    };

    //handle click in the first input of execute
    const onClick1 = () => {
        setCursorPos(input1Ref.current, "input1");
    }

    //handle click in the second input of execute
    const onClick2 =() => {
        setCursorPos(input2Ref.current, "input2");
    }

    return (
        <div className="info-panel-container">
            <div className="sentence">
                <table>
                    <tbody>
                        <tr>
                        <td align='right'>Expand</td>
                        <td align='left'>
                            <div className="VSCodeTextField-container">
                                <textarea
                                    ref={input1Ref}
                                    className="text-area"
                                    placeholder="definition"
                                    onKeyDown={handleKeyDown}
                                    onChange={handleChange}
                                    onClick={onClick1}
                                />
                            </div>
                        </td>
                        <td></td>
                        </tr>
                    </tbody>
                    <tbody>
                        <tr>
                        <td align='right'>in</td>
                        <td align='left'>
                            <div className="VSCodeTextField-container">
                                <textarea
                                    ref={input2Ref}
                                    className="text-area"
                                    placeholder="context"
                                    onKeyDown={handleKeyDown2}
                                    onChange={handleChange2}
                                    onClick={onClick2}
                                />
                            </div>
                        </td>
                        <td>
                            <div>
                                <VSCodeButton onClick={handleExecute}>{'\u23F5'}</VSCodeButton>
                            </div>
                        </td>
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



export default ExpandDefinition;
