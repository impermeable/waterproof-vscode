const { writeFileSync } = require("fs");

// Open the tactics file
const tactics = require("../completions/tactics.json");
const outputLocation = "../docs/tactics-sheet.md";

let mdContent = `# Waterproof Tactics Sheet\n\n`;

for (const tactic of tactics) {
    mdContent += `## \`${tactic.label}\`\n\n${tactic.description.replaceAll("*", "\\*")}\n\n`;

    if (tactic.example)
        mdContent += "```coq\n" + tactic.example + "\n```\n\n";
}

writeFileSync(outputLocation, mdContent);
