import { PpString } from "../../lib/types";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";

import "../styles/coqpp.css";


//function that can display a Pp string in the correct format
export function CoqPp({
  content,
  inline,
}: {
  content: PpString; //the content
  inline: boolean; //the location, either inline or not
}) {
  //if the content is already of string format it can be easily displayed
  if (typeof content == "string") {
    if (inline) {
      return <code style={{ whiteSpace: "pre" }}>{content}</code>;
    } else {
      return <pre className="coqpp">{content}</pre>;
    }
  } else {
    //if it is not a sring we use FormatPrettyPrint 
    //to find out more how to use this:
    // https://reactjs.org/docs/integrating-with-other-libraries.html
    if (inline) {
      let rendered = FormatPrettyPrint.pp2DOM(content, "horizontal");
      return (
        <div
          style={{ display: "inline" }}
          dangerouslySetInnerHTML={{ __html: rendered.prop("outerHTML") }}
        ></div>
      );
    } else {
      let rendered = FormatPrettyPrint.pp2DOM(content, "vertical");
      return (
        <div
          dangerouslySetInnerHTML={{ __html: rendered.prop("outerHTML") }}
        ></div>
      );
    }
  }
}
