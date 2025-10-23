import objectHash from "object-hash";
import { isMessage, Message } from "../../lib/types";
import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";

//message component that takes in a message as a PpString
export function Message({
  message,
}: {
  message: PpString | Message<PpString>;
}) {
  //hashing the message as the key
  const key = objectHash(message);
  //converting message to text if it is not of the type string
  const text =
    typeof message === "string"
      ? message
      : typeof message === "object" && "text" in message
      ? message.text
      : message;

  // Filter out the correct messages
  if (isMessage(message) && message.level !== 4) return;

  //every message is displayed as a CoqPp component
  if (Array.isArray(text)) {
    // Pp case
    return (
      <li key={key}>
        <CoqPp content={text} inline={true} />
      </li>
    );
  } else {
    // String case

    // Special messages that can occur
    const replace = "Hint, replace with: ";
    const insert = "Hint, insert: ";

    // If we have one of the messages as described above we show the text and the code
    // separately.
    if (text.startsWith(replace)) {
      return (
        <li key={key}>
          <p>Hint: <code>{text.substring(replace.length)}</code></p>
        </li>
      );
    } else if (text.startsWith(insert)) {
      return (<li key={key}>
        <p>Hint: <code>{text.substring(insert.length)}</code></p>
      </li>);
    }

    // If this is not a special message we just render as we normally would.
    return (<li key={key}>
      <CoqPp content={text} inline={true} />
      </li>);
  }
}
