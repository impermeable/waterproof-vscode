import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React, { useState, useEffect} from 'react';
import { Message, MessageType } from '../../shared';

// Import the JSON data containing the Coq tactics
import dataCoq from "../../completions/tactics.json";
// Import the new JSON data for Lean tactics
import dataLean from "../../completions/tacticsLean.json";

import '../styles/tactics.css';

const vscode = acquireVsCodeApi();

const ProofAssistant = () => {
    // State variable to track tactic visibility
    const [tacticVisibility, setTacticVisibility] = useState<Record<string, boolean>>({});
    const [value, setValue] = useState("");

    // State for the currently active tactics data (default to Coq)
    const [tacticsData, setTacticsData] = useState(dataCoq);

    // Listen for messages from the extension
    useEffect(() => {
        const handleMessage = (event: MessageEvent) => {
            const message = event.data as Message;
            if (message.type === MessageType.setTacticsMode) {
                if (message.body === 'lean') {
                    setTacticsData(dataLean);
                } else {
                    setTacticsData(dataCoq);
                }
                // Reset search and visibility when switching modes
                setTacticVisibility({});
                setValue(""); 
            }
        };

        window.addEventListener('message', handleMessage);

        // Request the current tactics mode immediately upon mounting
        vscode.postMessage({ 
            type: MessageType.command, 
            body: { command: "getTacticsMode", time: Date.now() } 
        });

        return () => window.removeEventListener('message', handleMessage);
    }, []);

    // Function to toggle tactic visibility
    const toggleVisibility = (tacticName: string) => {
        setTacticVisibility((prevState) => ({
            ...prevState,
            [tacticName]: !prevState[tacticName],
        }));
    };

    //handle button press of inserting a tactic
    const handleInsert = (event: React.MouseEvent, template: string) => {
        // log the name of the tactic
        vscode.postMessage({ time: Date.now(), type: MessageType.insert, body: { symbolLatex: template, symbolUnicode: template, type: "tactics" } });
    };

    //handle button press of copying a tactic to the clipboard
    const handleCopy = (event: React.MouseEvent, name: string) => {
        // put the tactic on the clipboard
        navigator.clipboard.writeText(name);
    };

    // Function to generate code for each tactic
    const generateCode = (tactic: any) => {
        const { label, description, example, template } = tactic;
        // FIXME: 
        const name = label;
        const isVisible = tacticVisibility[name];
        return (
            <div key={name} className="tactic-container">
                {/* The header contains the tactic name */}
                <div className="tactic-header">
                    <b>{name}</b>
                    <div className="button-group">
                        {/* There is a insert and copy button next to the tactic */}
                        <VSCodeButton className="tooltip" appearance="primary" onClick={(event) => handleCopy(event, name)}>
                            {'\u2398'}
                            <span className="tooltiptext">copy</span>
                        </VSCodeButton>
                        <VSCodeButton className="tooltip" appearance="primary" onClick={(event) => handleInsert(event, template)}>
                            {'\u270e'}
                            <span className="tooltiptext">insert</span>
                        </VSCodeButton>
                    </div>
                </div>
                <p className="tactic-description">
                    {/* The description of the tactic */}
                    <VSCodeButton appearance="icon" onClick={() => toggleVisibility(name)}>
                        {isVisible ? '\u25bc' : '\u25b6'}
                    </VSCodeButton>
                    {description}
                </p>
                {/* The example of the tactic, can be shown or hidden using isVisible */}
                {isVisible && (
                    <div className="tactic-example">
                        <pre>{example}</pre>
                    </div>
                )}
                <VSCodeDivider />
            </div>
        );
    };

    const handleKeyDown = (event: React.KeyboardEvent<HTMLTextAreaElement>) => {
        if (event.key === 'Enter' && event.shiftKey) {
            // Handle Shift + Enter key press logic here
            // Prevent adding a new line in the textarea
            event.preventDefault();
        }
    };

    // If text get added, filter
    const handleChange = (event: React.ChangeEvent<HTMLTextAreaElement>) => {
        setValue(event.target.value);
    };

    const handleClick = () => {
    }

    // The text area to filter the tactics
    return (
        <><div className='text-box'>
            <div className='filter'>
                Filter: </div> <textarea
                className="text-area"
                cols={50}
                placeholder="Filter tactics"
                onKeyDown={handleKeyDown}
                onChange={handleChange}
                onClick={handleClick} />
        </div><div className="proof-assistant">
                {/* here we filter the data based on the active tacticsData */}
                {tacticsData.filter(item => item.label.toLowerCase().includes(value.toLowerCase())).map((tactic) => generateCode(tactic))}
            </div></>
        );
};

export default ProofAssistant;
