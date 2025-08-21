import $ from "jquery";
import { PropsWithChildren, useLayoutEffect, useRef } from "react";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import { convertToString, Goal, GoalConfig, Hyp, HypVisibility, PpString } from "../../lib/types";
import { Box } from "./Box";
import { CoqPp } from "./CoqPp";
import { HypEl } from "../debug/Hypothesis"
import { MessageType } from "../../shared";

import {
  Position,
  VersionedTextDocumentIdentifier
} from "vscode-languageserver-types";
import "../styles/goals.css";

const vscode = acquireVsCodeApi();

//type that contains Goal<PpString> and an ID for that goal
type GoalP = { goal: Goal<PpString>; idx: number;};

//component to display a single goal as a Pp string
function Goal({ goal}: GoalP) {
  // https://beta.reactjs.org/learn/manipulating-the-dom-with-refs
  const ref: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  const tyRef: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  //callback to allow scrolling
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
  });

  // Check if goal.ty starts with the required string
  const tyString = convertToString(goal.ty);

  const options = [];
  // Use regex to extract suggestion
  const regex = /Add the following line to the proof:\s*(\S([^.]*?)\.(.*\n)?)/;
  const match = tyString.match(regex);
  console.log("matches", match);
  if (match) {
    options.push(match[1].trim());
  }
  // Same for the option after "or write:"
  const regex2 = /or write:\s*(\S.[^.]*?\.[^a-zA-Z]*?)if/;
  const match2 = tyString.match(regex2);
  if (match2) {
    options.push(match2[1].trim());
  }

  // Handler for insert button
  const handleInsert = (suggestion : string) => {
    // Post insert message with the line as symbolUnicode and type "tactics"
    vscode.postMessage({ 
      time: Date.now(),
      type: MessageType.insert, 
      body: { 
        symbolUnicode: suggestion,
        type: "tactics" 
      }
    });
  };

  return (
    <div className="coq-goal-env" ref={ref}>
      <div style={{ marginLeft: "1ex" }} ref={tyRef}>
        <CoqPp content={goal.ty} inline={false} />
        {
          options.map((option, index) => (
          <div key={index}>
            <button
              className="goal-insert-btn"
              onClick={handleInsert.bind(null, option)}
            >
              Adapt suggestion{index == 0 ? "" : " " + (index + 1)}
            </button>
          </div>
          ))
        }
      </div>
    </div>
  );
}

//type for list of goals that can pass children from one component to the next
//show_on_empty is used to determine if we want to show that there are no goals of that kind
type GoalsListP = PropsWithChildren<{
  goals: Goal<PpString>[];
  header: string;
  show_on_empty: boolean;
  bullet_msg?: PpString;
  pos: Position
  textDoc: VersionedTextDocumentIdentifier
  visibility: HypVisibility
}>;

//function that displays a list of goals if it exists
function GoalsList({
  goals,
  header,
  show_on_empty,
  bullet_msg,
  pos,
  textDoc,
  visibility
}: GoalsListP) {
  const count = goals.length;

  const hyps : (goal : Goal<PpString>) => Array<Hyp<PpString>> = (goal : Goal<PpString>) => {
      const hyps : Array<Hyp<PpString>> = [];
      if (visibility === HypVisibility.All) {
        hyps.push(...goal.hyps);
      } else if (visibility === HypVisibility.Limited) {
        hyps.push(
          ...goal.hyps
            .map (hyp => 
              // Filter out all names starting with an underscore
              ({ ...hyp, names: hyp.names.filter(name => convertToString(name).charAt(0) !== "_") }))
            .filter(hyp => hyp.names.length > 0)
        ); 
      }
      return hyps;
  }
  const hypBlock = (goal : Goal<PpString>) => {
    const elems = hyps(goal).map((hyp, _) => 
          <HypEl hyp={hyp} key={hyp.names[0].toString()} />)
    if (elems.length > 0) {
      return <Box summary={`We know: `} pos={pos} textDox={textDoc}>
          { elems }
      </Box>
    }
    return elems;
  }

  //if there are no goals then this is displayed
  if (count == 0) {
    if (show_on_empty) {
      return (
        <Box summary="Proof finished" pos={pos} textDox={textDoc}>{bullet_msg ? (
          <div className="aside">
            <CoqPp content={bullet_msg} inline={true} />
          </div>
        ) : null}</Box>
      );
    } else {
      return null;
    }
  //One goal, the goals is displayed
  } else if (count == 1) {
    return (
      <div>
        <Box summary={`${header}`} pos={pos} textDox={textDoc}>
          <Goal key={0} goal={goals[0]} idx={0}/>
        </Box>
        {hypBlock(goals[0])}
      </div>

    );
  //Numerous goals, only the first goal is displayed, the other goals are hidden.
  } else {
    return (
      <div>
        <Box summary={`${header}`} pos={pos} textDox={textDoc}>
          <Goal key={0} goal={goals[0]} idx={0}/>
        </Box>
        {hypBlock(goals[0])}
        <Box summary={`Afterwards, we need to complete other subproofs`} pos={pos} textDox={textDoc}>
        </Box>
      </div>
    );
  }

}

function GoalsRemaining({
  goals,
  header,
  show_on_empty,
  bullet_msg,
  pos,
  textDoc
}: GoalsListP) {
  const count = goals.length;

  //if there are no goals then this is displayed
  if (count == 0) {
    if (show_on_empty) {
      return (
        <Box summary="Proof finished" pos={pos} textDox={textDoc}>{bullet_msg ? (
          <div className="aside">
            <CoqPp content={bullet_msg} inline={true} />
          </div>
        ) : null}</Box>
      );
    } else {
      return null;
    }
  }

  //if thare are goals then this maps over the goals and display them by using the Goal component
  return (
    <Box summary={`${header}`} pos={pos} textDox={textDoc}>
    </Box>
  );
}
//type that has an id, position, document, and the stacked goal that also takes its parents
type StackSummaryP = PropsWithChildren<{
  idx: number;
  stack: [Goal<PpString>[], Goal<PpString>[]][];
  pos: Position
  textDoc: VersionedTextDocumentIdentifier
  visibility: HypVisibility
}>;

//goals can have multiple layers which are stacked.
//the following function handles the display of stacked goals
function StackGoals({ idx, stack, pos, textDoc, visibility }: StackSummaryP) {
  const count = stack.length;
  if (count <= idx) return null;

  const [l, r] = stack[idx];
  const goals = l.concat(r);

  if (idx == 0) {
    return (
      <div>
        {/* uses GoalsList to show the goals as a list within a stack */}
        <GoalsRemaining
          goals={goals}
          header={`Afterwards, we need to complete other subproofs`}
          show_on_empty={false}
          pos={pos}
          textDoc={textDoc}
          visibility={visibility}
        />
      </div>
    );
  } else {
    return (
      <div>
        {/* uses GoalsList to show the goals as a list within a stack */}
        <GoalsRemaining
          goals={goals}
          header={`Afterwards, we need to complete other subproofs`}
          show_on_empty={false}
          pos={pos}
          textDoc={textDoc}
          visibility={visibility}
        />
      </div>
    )
    }
  }
//type that has goals, position and textdocument and takes its children
type GoalsParams = PropsWithChildren<{ goals?: GoalConfig<PpString>, pos: Position, textDoc: VersionedTextDocumentIdentifier, visibility: HypVisibility }>;

//the component that is used by other components
//uses both the stackgoals for the goals at different levels and the GoalsList for the goals that consist of a list
export function Goals({ goals, pos, textDoc, visibility }: GoalsParams) {
  //if there are no goals, the user is shown "No goals at this point."
  if (!goals) {
    return <Box summary="We need to show" pos={pos} textDox={textDoc}>
      No goals at this point.
    </Box>
  }

  const count = goals.goals.length

  if (count <= 1) {
    return (
      <div className="goal-panel">
        {/* primary list of goals */}
        <GoalsList
          goals={goals.goals}
          header={"We need to show"}
          show_on_empty={true}
          bullet_msg={goals.bullet}
          pos={pos}
          textDoc={textDoc}
          visibility={visibility}
        />
        {/* stacking goals that are on different levels */}
        <div style={{ marginLeft: "0.5ex" }}>
          <StackGoals idx={0} stack={goals.stack} pos={pos} textDoc={textDoc} visibility={visibility} />
        </div>
        <div style={{ marginLeft: "0.5ex" }}>
          {/* a list for the goals that are on the shelf */}
          <GoalsList
            goals={goals.shelf}
            header={"Shelf"}
            show_on_empty={false} // these goals are not shown if they do not exist
            pos={pos}
            textDoc={textDoc}
            visibility={visibility}
          />
          {/* a list for the goals that are given up */}
          <GoalsList
            goals={goals.given_up}
            header={"Given Up"}
            show_on_empty={false} // these goals are not shown if they do not exist
            pos={pos}
            textDoc={textDoc}
            visibility={visibility}
          />
        </div>
      </div>
    );
  } else {

    return (
      <div className="goal-panel">
        {/* primary list of goals */}
        <GoalsList
          goals={goals.goals}
          header={"We need to show"}
          show_on_empty={true}
          bullet_msg={goals.bullet}
          pos={pos}
          textDoc={textDoc}
          visibility={visibility}
        />

        <div style={{ marginLeft: "0.5ex" }}>
          {/* a list for the goals that are on the shelf */}
          <GoalsList
            goals={goals.shelf}
            header={"Shelf"}
            show_on_empty={false} // these goals are not shown if they do not exist
            pos={pos}
            textDoc={textDoc}
            visibility={visibility}
          />
          {/* a list for the goals that are given up */}
          <GoalsList
            goals={goals.given_up}
            header={"Given Up"}
            show_on_empty={false} // these goals are not shown if they do not exist
            pos={pos}
            textDoc={textDoc}
            visibility={visibility}
          />
        </div>
      </div>
    );
  }
}
