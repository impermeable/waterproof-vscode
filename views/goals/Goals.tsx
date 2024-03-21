import $ from "jquery";
import objectHash from "object-hash";
import { PropsWithChildren, useLayoutEffect, useRef } from "react";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import { Goal, GoalConfig, PpString } from "../../lib/types";
import { Box } from "./Box";
import { CoqPp } from "./CoqPp";

import {
  Position,
  VersionedTextDocumentIdentifier
} from "vscode-languageserver-types";
import "../styles/goals.css";

//type that contains Goal<PpString> and an ID for that goal
type GoalP = { goal: Goal<PpString>; idx: number; };

//component to display a single goal as a Pp string
function Goal({ goal }: GoalP) {
  // https://beta.reactjs.org/learn/manipulating-the-dom-with-refs
  const ref: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  const tyRef: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  //callback to allow scrolling
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
    // See Pfff.v:17160 for tests.
  });

  return (
    <div className="coq-goal-env" ref={ref}>
      <div style={{ marginLeft: "1ex" }} ref={tyRef}>
        <CoqPp content={goal.ty} inline={false} />
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
}>;

//function that displays a list of goals if it exists 
function GoalsList({
  goals,
  header,
  show_on_empty,
  bullet_msg,
  pos,
  textDoc
}: GoalsListP) {
  let count = goals.length;

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
      {goals.map((value, idx) => {
        let key = objectHash(value);
        return <Goal key={key} goal={value} idx={idx + 1} />;
      })}
    </Box>
  );
}
//type that has an id, position, document, and the stacked goal that also takes its parents
type StackSummaryP = PropsWithChildren<{
  idx: number;
  stack: [Goal<PpString>[], Goal<PpString>[]][];
  pos: Position
  textDoc: VersionedTextDocumentIdentifier
}>;

//goals can have multiple layers which are stacked. 
//the following function handles the display of stacked goals
function StackGoals({ idx, stack, pos, textDoc }: StackSummaryP) {
  let count = stack.length;
  if (count <= idx) return null;

  const [l, r] = stack[idx];
  const goals = l.concat(r);
  //defines the level of the goal using idx
  let level_indicator =
    idx === 0 ? "the same bullet level" : `the -${idx} bullet level`;

  return (
    <div>
      <Box summary={`Afterwards, we need to complete other subproofs`} pos={pos} textDox={textDoc}>
      </Box>
    </div>
  );
}
//type that has goals, position and textdocument and takes its children 
type GoalsParams = PropsWithChildren<{ goals?: GoalConfig<PpString>, pos: Position, textDoc: VersionedTextDocumentIdentifier }>;

//the component that is used by other components
//uses both the stackgoals for the goals at different levels and the GoalsList for the goals that consist of a list
export function Goals({ goals, pos, textDoc }: GoalsParams) {
  //if there are no goals, the user is shown "Nothing to show at this point"
  if (!goals) {
    return <Box summary="We need to show:" pos={pos} textDox={textDoc}>
      Nothing to show at this point.
    </Box>
  }

  return (
    <div className="goal-panel">
      {/* primary list of goals */}
      <GoalsList
        goals={goals.goals}
        header={"We need to show:"}
        show_on_empty={true}
        bullet_msg={goals.bullet}
        pos={pos}
        textDoc={textDoc}
      />
      {/* stacking goals that are on different levels */}
      <div style={{ marginLeft: "0.5ex" }}>
        <StackGoals idx={0} stack={goals.stack} pos={pos} textDoc={textDoc} />
      </div>
    </div>
  );
}
