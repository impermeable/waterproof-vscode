import objectHash from "object-hash";
import { GoalAnswer, Message as Msg, Pp } from "../../lib/types";
import { PpString } from "../../lib/types";
import { Message } from "./Message";
import {Box} from "./Box";
import "../styles/messages.css";
import { PropsWithChildren } from "react";

//type that makes a GoalAnswer<PpString> also takes its childrens components with
export type MessagesInfo = PropsWithChildren<
  {
    answer: GoalAnswer<PpString>
  } 
>;

//component that takes in the MessagesInfo and displays the list of messages
export function Messages({answer} : MessagesInfo) {
  let count = answer.messages.length;
  //check if there are any messages that need to be shown
  if (count != 0) {
  //the Box component is used to display the messages along with the location
  return (
    <Box summary={`Messages`} pos={answer.position} textDox={answer.textDocument} >
      <ul className="messageList">
        {answer.messages.map((value, idx) => {
          //mapping over the messages to display the list of all messages
          //hashing the value to retrieve a key
          let key = objectHash(value);
          return <Message key={key} message={value} />;
        })}
      </ul>
    </Box>
  );
      }
  else {return null}
}
