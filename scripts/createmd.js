const { writeFileSync } = require("fs");
const tactics = require("../shared/completions/tactics.json");
const pdfLocation = "tactics.md";

let mdContent = `# Waterproof Tactics\n\n`;

for (const tactic of tactics) {
    mdContent += `## \`${tactic.label}\`\n\n${tactic.description.replaceAll("*", "\\*")}\n\n`;

    if (tactic.example)
        mdContent += "```coq\n" + tactic.example + "\n```\n\n";
}

writeFileSync(pdfLocation, mdContent);
