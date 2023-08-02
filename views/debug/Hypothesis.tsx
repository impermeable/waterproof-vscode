import $ from "jquery";
import objectHash from "object-hash";
import { PropsWithChildren, useLayoutEffect, useRef } from "react";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import { GoalConfig, Hyp, PpString } from "../../lib/types";
import { Box } from "../goals/Box";
import { CoqPp } from "../goals/CoqPp";

import React from "react";
import {
  Position,
  VersionedTextDocumentIdentifier
} from "vscode-languageserver-types";
import "../styles/goals.css";

type CoqId = PpString;

//displays the hypothesis as a pp string
function Hyp({ hyp: { names, def, ty } }: { hyp: Hyp<PpString> }) {
  //className to give the right css to the hypothesis, definition or not
  let className = "coq-hypothesis" + (def ? " coq-has-def" : "");
  //a label for the hypothesis
  let mkLabel = (id: CoqId) => <label key={objectHash(id)}>{id}</label>;
  //this converts the PpString to a CoqPp component
  let mkdef = (pp?: PpString) =>
    pp ? (
      <span className="def">
        <CoqPp content={pp} inline={true} />
      </span>
    ) : null;


  return (
    <div className={className}>
      {/* //mapping the names to labels */}
      {names.map(mkLabel)}
      {mkdef(def)}
      {/* displaying the actual contect as a CoqPp component */}
      <div>
        <CoqPp content={ty} inline={true} />
      </div>
    </div>
  );
}

//type for array of Hyp<PpString>
type HypsP = { hyps: Hyp<PpString>[] };
//maps through the list of hypotheses
function Hyps({ hyps }: HypsP) {
  return (
    <>
      {hyps.map((v) => {
        let key = objectHash(v);
        return <Hyp key={key} hyp={v} />;
      })}
    </>
  );
}
//type that has the goals, position and textdocument and takes its children 
type GoalsParams = PropsWithChildren< { goals?: GoalConfig<PpString>, pos: Position, textDoc:VersionedTextDocumentIdentifier }>;

//the exported Hypothesis funtion that takes in a GoalsParams
export function Hypothesis({ goals, pos, textDoc }: GoalsParams) {
  // https://beta.reactjs.org/learn/manipulating-the-dom-with-refs
  const ref: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  const tyRef: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
    // See Pfff.v:17160 for tests.
    if (tyRef.current) {
      tyRef.current.scrollIntoView();
    }
  });

  //checking of goals and hypotheses exist
  if (!goals) return null;
  if (!goals.goals) {
    return <Box summary="Hypothesis" pos={pos} textDox={textDoc}>
    No hypothesis at this point.
  </Box>
  }
  //if a goal does exist the Box component is used to display them
  //the list of hypothesis is mapped to display all hypothesis that are connected to a goal
  return (
    <div className="coq-goal-env" ref={ref}>
    <Box summary={'Hypothesis'} pos={pos} textDox={textDoc}>
      {goals.goals.map((value, idx) => {
        let key = objectHash(value);
        //another chekc for when a goal does not have hypothesis
        if (value.hyps.length ==0 ) return "No Hypothesis at this point!";
        else return <Hyps hyps={value.hyps} key={key}/>
        })}
      </Box>
    </div>
  );
}



