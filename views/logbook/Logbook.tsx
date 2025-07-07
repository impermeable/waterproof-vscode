import objectHash from "object-hash";
import React, { useEffect, useState } from 'react';

import { GoalAnswer, PpString } from "../../lib/types";
import { Messages } from "../goals/Messages";

import "../styles/info.css";
import { Message, MessageType } from "../../shared";


export function Logbook() {
  //saves the goals for the logbook
  const [goalsArray, setGoalsArray] = useState<GoalAnswer<PpString>[]>();
  //boolean to check if the messages are still loading
  const [isLoading, setIsLoading] = useState(true);

  //message handler
  function infoViewDispatch(msg: Message) {
    if (msg.type === MessageType.renderGoalsList) {
      setGoalsArray(msg.body.goalsList); //setting the information
      setIsLoading(false); //putting loading to false
    }
  }

  // Set the callback
  useEffect(() => {
    const callback = (ev: MessageEvent<Message>) => {infoViewDispatch(ev.data);};
    window.addEventListener("message", callback);
    return () => window.removeEventListener("message", callback);
  }, []);

  //show that the messages are loading
  if (isLoading) return <div>Loading...</div>;

  if (!goalsArray) return null;

  //when messages are loaded, we map over them and display them with the Messages component
  return (
    <div className="info-panel-container">
      <div className="info-panel">
      {goalsArray.map((value, _) => {
          const key = objectHash(value);
          return <Messages key={key} answer={value} />;
        })}
      </div>
    </div>
  );
}

export default Logbook;
