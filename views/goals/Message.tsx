import objectHash from "object-hash";
import { Message } from "../../lib/types";
import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";

//message component that takes in a message as a PpString
export function Message({
  message,
}: {
  message: PpString | Message<PpString>;
}) {
  //hashing the message as the key
  let key = objectHash(message);
  //converting message to text if it is not of the type string
  let text =
    typeof message === "string"
      ? message
      : typeof message === "object" && "text" in message
      ? message.text
      : message;

      //every message is displayed as a CoqPp component
  return (
    <li key={key}>
      <CoqPp content={text} inline={true} />
    </li>
  );
}
