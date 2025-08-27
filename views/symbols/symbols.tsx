import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React, { useState } from "react";
import { MessageType } from '../../shared';
import "../styles/info.css";
// Get the button data
import data from "../../shared/completions/symbols.json";

const vscode = acquireVsCodeApi();

export function Symbols() {
    // Map the symbols to an array of tupels that contain a number (category), string (id) and string (title)

    const buttonArray: [number, string, string][] = data.map((value) => {
        const {label, symbolPanelCategory, apply} = value;
        return [symbolPanelCategory as number, label, apply];
    });

    // FIXME: Does this state do anything?
    const [_tooltip, setTooltip] = useState('');

    // Insert symbol when pressed
    const handleInsert = (event, id, title) => {
        // A message containing the current time, type, and the symbol to be inserted is send 
        vscode.postMessage({ time: Date.now(), type: MessageType.insert, body: { symbolLatex: id, symbolUnicode: title, type: "symbol" } });
    };

    // Set tooltip when hover
    const handleMouseEnter = (event, id) => {
        // The tooltip shows the id, this is the latex command of the symbol
        setTooltip(id);
    };

    // Remove tooltop when not hover
    const handleMouseLeave = () => {
        setTooltip('');
    };

    // We map the tuples to the buttons, 
    // the id is used for the tooltip and the title is used as the character    
    const generateButtons = (category: number) => {
        const symbols = buttonArray.filter(([cat]) => cat === category);
        return symbols.map(([, id, title]: [number, string, string]) => (
            <VSCodeButton
                className="tooltip"
                appearance="icon"
                id={id}
                key={id}
                onClick={(event) => handleInsert(event, id, title)}
                onMouseEnter={(event) => handleMouseEnter(event, id)}
                onMouseLeave={handleMouseLeave}
            >
                {title}
                <span className="tooltiptext">{id}</span>
            </VSCodeButton>
        ));
    };

    // here we create all the button groups by their category number
    const normalButtons = generateButtons(0);
    const capitalButtons = generateButtons(1);
    const mathButtons = generateButtons(2);
    const arrowButtons = generateButtons(3);
    const numberButtons = generateButtons(4);
    const supSubButtons = generateButtons(5);
    const calligraphicButtons = generateButtons(6);

    return (
        <div className="info-panel-container">
            <div id="view-1">
                <p>Normal Greek Letters</p>
            </div>
            <div>
                {normalButtons}
            </div>
            <VSCodeDivider />
            {/* The capital greek letters */}
            <div id="view-2">
                <p>Capital Greek Letters</p>
            </div>
            <div>
                {capitalButtons}
            </div>
            <VSCodeDivider />
            <div id="view-6">
                <p>Calligraphic Letters</p>
            </div>
            <div>
                {calligraphicButtons}
            </div>
            <VSCodeDivider />
            {/* Math symbol buttons */}
            <div id="view-3">
                <p>Mathematical Symbols</p>
            </div>
            <div>
                {mathButtons}
            </div>
            <VSCodeDivider />
            {/* Arrow buttons */}
            <div id="view-4">
                <p>Arrow Symbols</p>
            </div>
            <div>
                {arrowButtons}
            </div>
            <VSCodeDivider />
            {/* And the number sysbols buttons */}
            <div id="view-5">
                <p>Number System Symbols</p>
            </div>
            <div>
                {numberButtons}
            </div>
            <VSCodeDivider />
            {/* And the superscript and subscript buttons */}
            <div id="view-6">
                <p>Superscript and Subscript</p>
            </div>
            <div>
                {supSubButtons}
            </div>
        </div>
    );
}

export default Symbols;