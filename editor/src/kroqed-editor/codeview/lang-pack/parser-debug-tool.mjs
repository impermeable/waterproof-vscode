
import {parser} from "./syntax";

function parse(input) {
    return parser.parse(input);
}

function printJSON(input) {
  console.log(JSON.stringify(parser.parse(input), null, 2));
}

import { readFileSync } from "fs";

const fileContents = readFileSync("input.txt", "utf8");
console.log("File contents:");
console.log(fileContents);
console.log("JSON");
printJSON(fileContents);