import React from "react";
import { GoalAnswer, GoalRequest, Pp, PpString } from "../../lib/types";
import { PropsWithChildren, DetailsHTMLAttributes } from "react";
import "../styles/box.css";
import {
  VersionedTextDocumentIdentifier,
  Position,
  Range,
} from "vscode-languageserver-types";

//type that makes sure the children components are also passed 
export type DetailsP = PropsWithChildren<
  {
    summary: React.ReactNode;
    pos: Position //the position within the file (line number and character)
    textDox: VersionedTextDocumentIdentifier //the file
  } 
>;


//Modular component that can be used to display info together with the location
//the summmary is the title of the box
//children are all child components
//position is the position in the textdocument
//textDox is the corresponding file
export function Box({ summary, children, pos, textDox  }: DetailsP) {
    let uri = textDox.uri.split("/").slice(-1)[0];
    let line = pos.line + 1; // 1-based position
    let character = pos.character + 1; // 1-based character
    let info = (
    <span>
      {uri}:{line}:{character}
    </span>
    )
  return (
    <div className="box">
      <div className="box__header">
        {summary}
        <div className="box__header__info">{info}</div>
      </div>
      <div className="box__content">
        {children}
      </div>
    </div>
  );
}

export default Box;