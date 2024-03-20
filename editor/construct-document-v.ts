import { topLevelBlocksV } from "./src/kroqed-editor/prosedoc-construction/construct-document";
import { readFileSync, writeFileSync } from "fs";

const input = readFileSync("document.v", "utf-8");

// Print the blocks to the console
const blocks = topLevelBlocksV(input);
for (const block of blocks) {
    block.debugPrint(0);
}
