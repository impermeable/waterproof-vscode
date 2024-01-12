import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React, { useEffect, useRef, useState } from "react";
import { GoalAnswer, PpString } from "../../lib/types";
import { MessageType } from '../../shared';
import { Messages } from "../goals/Messages";
import "../styles/execute";

const date = new Date();
const vscode = acquireVsCodeApi();

export function Execute() {
    // create the states for the components that need them
    const [cursor, setCursor] = useState(0);
    const [value, setValue] = useState("");
    const [info, setInfo] = useState<GoalAnswer<PpString>>();
    const [isLoading, setIsLoading] = useState(false)

    // create a reference to the textarea element
    const textareaRef = useRef(null);

    // callback that handles the message
    // so we can access it within the component
    useEffect(() => {
        const handleMessage = (event) => {
            switch (event.data.type) {
                //insert message
                case MessageType.insert:
                    insertText(event.data.body.symbolUnicode);
                    break;
                //info after execute message
                case MessageType.command:
                    setInfo(event.data.body);
                    setIsLoading(false);
                    break;
            }
        };

        // We listen for messages from the window
        window.addEventListener('message', handleMessage);

        return () => {
            window.removeEventListener('message', handleMessage);
        };
    }, [cursor, value]);

    //setting the cursor position and the value of the text area
    const setCursorPos = (textarea) => {
        if (textarea) {
            const startPos = textarea.selectionStart;
            const val = textarea.value;
            setCursor(startPos);
            setValue(val);
        }
    }

    //inserting in the search bar
    const insertText = (textToInsert: string) => {
        const textarea = textareaRef.current;
        if (textarea) {
            // We find the new cursor position
            const newValue =
                value.substring(0, cursor) +
                textToInsert +
                value.substring(cursor, value.length);
            (textarea as HTMLTextAreaElement).value = newValue;
            (textarea as HTMLTextAreaElement).setSelectionRange(cursor + textToInsert.length, cursor + textToInsert.length);
            (textarea as HTMLTextAreaElement).focus();
            //update the states with the cursor posistions
            setValue(newValue);
            setCursor(cursor + textToInsert.length);
        }
    };

    const handleExecute = () => {
        // Handle execute logic with the inputText here
        console.log('Execute command:', value.replace(/\.\s*$/s, ''));
        vscode.postMessage({ time: date.getTime(), type: MessageType.command, body: value.replace(/\.\s*$/s, '') });
        setIsLoading(true);
    };

    const handleKeyDown = (event) => {
        if (event.key === 'Enter' && event.shiftKey) {
            // Handle Shift + Enter key press logic here
            console.log('Shift + Enter pressed:', event.target.value);
            // Prevent adding a new line in the textarea
            event.preventDefault();
        }
        setCursorPos(textareaRef.current);
    };

    // handle the change in the execute bar
    const handleChange = (event) => {
        // update the values accordingly
        setValue(event.target.value);
        setCursorPos(textareaRef.current)
    };

    //hanles click in the execute bar
    const handleClick = () => {
        setCursorPos(textareaRef.current);
    }

    return (
        <div className="info-panel-container">
            {/* create the input area to execute things */}
            <div className="sentence">
                <textarea
                    ref={textareaRef}
                    className="text-area"
                    cols={50}
                    placeholder="Execute in isolation"
                    onKeyDown={handleKeyDown}
                    onChange={handleChange}
                    onClick={handleClick}
                />
                <br />
                <VSCodeButton onClick={handleExecute}>Execute</VSCodeButton>
            </div>
            {/* Get a loading indication */}
            {isLoading ? (
                <div className="sentence">Loading...</div>
            ) : (
                <>
                    {/* Once done with loading, show the results */}
                    {Array.isArray(info) && info !== undefined && (
                        <React.Fragment>
                            {/* Displaying the first element of the info array */}
                            {info[0]}
                            <VSCodeDivider />
                        </React.Fragment>
                    )}
                    {info !== undefined && !Array.isArray(info) && (
                        <React.Fragment>
                            {/* Rendering the Messages component with the info */}
                            <Messages answer={info} />
                            <VSCodeDivider />
                        </React.Fragment>
                    )}
                </>
            )}
        </div>
    );
}

export default Execute;
