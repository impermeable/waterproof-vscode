import { VSCodeButton, VSCodeDivider } from '@vscode/webview-ui-toolkit/react';
import React from "react";
import { GoalAnswer, PpString } from "../../lib/types";
import "../styles/execute.css";
import { Messages } from '../goals/Messages';

type HelpParams = {
  helpInfo?: string[] | GoalAnswer<PpString>;
  isLoading: boolean;
  onRequestHelp: () => void;
};

export function Help({ helpInfo, isLoading, onRequestHelp }: Readonly<HelpParams>) {
    const hasNoResults = Array.isArray(helpInfo) && helpInfo.length === 0;
    return (
        <div className="info-panel-container">
            <div className="sentence">
              {/* help button */}
              <VSCodeButton onClick={onRequestHelp}>Help</VSCodeButton>
            </div>
            {/* when loading show loading */}
            {isLoading ? (
            <div className="sentence">Loading...</div>
            ) : (
            <>
            {/* when done show results */}
            {hasNoResults ? (
                <div>No results</div>
                ) : (
                    <>
                    {Array.isArray(helpInfo)  && helpInfo !== undefined && (
                   <React.Fragment>
                     {helpInfo[0]}
                     <VSCodeDivider />
                   </React.Fragment>
                 )}
                     {helpInfo !== undefined && !Array.isArray(helpInfo) &&(
                       <React.Fragment>
                         <Messages answer={helpInfo} />
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
