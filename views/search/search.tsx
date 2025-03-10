import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React, { useEffect, useRef, useState } from "react";

import { Message, MessageType } from "../../shared";
import "../styles/execute.css";
import { Messages } from '../goals/Messages';

const date = new Date();
const vscode = acquireVsCodeApi();

export function Search() {
    // create the states for the components that need them
    const [searchText, setSearchText] = useState("");
    const [cursorSearch, setCursorSearch] = useState(0);
    const [info, setInfo] = useState([""]);
    const [current, setCurrent] = useState("");
    const [isLoading, setIsLoading] = useState(false);

    const searchareaRef =  useRef(null);

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
      }, [ cursorSearch, searchText, current, info ]);

      // the cursor position is updated together with the current textarea
      const setCursorPos = (textarea, cur) => {
        setCurrent(cur);
        if (textarea) {
            const startPos = textarea.selectionStart;
            const val = textarea.value;
            setCursorSearch(startPos);
            setSearchText(val);
        }
    }

    //inserting text at the previous cursor position
    const insertText = (textToInsert: string) => {
        let textarea = null;
        let cursor = 0;
        let value = "";
        textarea = searchareaRef.current;
        cursor = cursorSearch;
        value = searchText;
        if (textarea) {
            const newValue = value.substring(0, cursor) +textToInsert +value.substring(cursor, value.length);
            (textarea as HTMLTextAreaElement).value = newValue;
            (textarea as HTMLTextAreaElement).setSelectionRange(cursor+textToInsert.length, cursor+textToInsert.length);
            (textarea as HTMLTextAreaElement).focus();
            //handles the insertion in the current text area
            // search input area
            setSearchText(newValue);
            setCursorSearch(cursor +textToInsert.length);
        }
    };

    //button press search
    const handleSearch = () => {
        vscode.postMessage({time: date.getTime(), 
                            type: MessageType.command, 
                            body: `Search "${searchText.replace(/(\.\s*|\s*)$/s, '')}".`})
        setIsLoading(true);
    }

    //search by pressing shift + enter
    const handleKeyDownSearch = (event) => {
        if (event.key === 'Enter' && event.shiftKey) {
            // Handle Shift + Enter key press logic here
            // Prevent adding a new line in the textarea
            event.preventDefault(); 
             //print the search results
        }
        setCursorPos(searchareaRef.current, "search");
    };

    //handle change in the search input
    const handleChangeSearch = (_) => {
        setCursorPos(searchareaRef.current, "search");
    };

    // handle click in the search bar
    const onClickSearch = ()=> {
        setCursorPos(searchareaRef.current, "search");
    }

    return (
        <div className="info-panel-container">
            <div className="sentence">
                <table>
                    <tbody>
                        <tr>
                        <td align='right'>Search</td>
                        <td align='left'>
                            <div className="VSCodeTextField-container">
                                <textarea
                                    id="searcharea"
                                    ref={searchareaRef}
                                    className="text-area"
                                    placeholder="term"
                                    onKeyDown={handleKeyDownSearch}
                                    onChange={handleChangeSearch}
                                    onClick={onClickSearch}
                                />
                            </div>
                        </td>
                        <td>
                            <div>
                                <VSCodeButton id="search" onClick={handleSearch}><div>&#x1F50E;&#xFE0E;</div></VSCodeButton>
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



export default Search;
