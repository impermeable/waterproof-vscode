import { topLevelBlocks } from "./src/kroqed-editor/prosedoc-construction/construct-document";
import { readFileSync, writeFileSync } from "fs";

const input = readFileSync("document.mv", "utf-8");

// Print the blocks to the console
const blocks = topLevelBlocks(input);
for (const block of blocks) {
    block.debugPrint(0);
}
