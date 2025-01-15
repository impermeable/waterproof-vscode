import objectHash from "object-hash";
import React, { useEffect, useState } from 'react';

import { GoalAnswer, PpString } from "../../lib/types";
import { Messages } from "../goals/Messages";
import { InfoError, WaitingForInfo } from "../lib/CoqMessage";

import "../styles/info.css";


interface RenderGoalsArray {
  type: "renderGoals";
  body: GoalAnswer<PpString>[];
}
interface CoqMessageEvent extends MessageEvent {
  data: RenderGoalsArray | WaitingForInfo | InfoError;
}


export function Logbook() {
  //saves the goals for the logbook
  const [goalsArray, setGoalsArray] = useState<GoalAnswer<PpString>[]>();
  //boolean to check if the messages are still loading
  const [isLoading, setIsLoading] = useState(true);

  //message handler
  function infoViewDispatch(event: CoqMessageEvent) {
    if (event.data.type === "renderGoals") {
      setGoalsArray(event.data.body); //setting the information
      setIsLoading(false); //putting loading to false
    } else if (event.data.type === "waitingForInfo") {
      setIsLoading(true); //waiting for info therefore loading is true
    }
  }

  // Set the callback
  useEffect(() => {
    window.addEventListener("message", infoViewDispatch);
    return () => window.removeEventListener("message", infoViewDispatch);
  }, []);

  //show that the messages are loading
  if (isLoading) return <div>Loading...</div>;

  if (!goalsArray) return null;

  //when messages are loaded, we map over them and display them with the Messages component
  return (
    <div className="info-panel-container">
      <div className="info-panel">
      {goalsArray.map((value, idx) => {
          const key = objectHash(value);
          return <Messages key={key} answer={value} />;
        })}
      </div>
    </div>
  );
}

export default Logbook;
