

const document = `# Test title markdown

\`\`\`coq
(** This should turn into a coqdoc thing *)
Lemma this_should_be_coqcode.
\`\`\`
$$This should turn into a math_display$$

this should turn into $math_inline$ and markdown.

<input-area>
All rules apply as above, but should be contained in 'input' type node.
</input-area>

<hint title="title">
All rules apply as above, but should be contained in 'hint' type node with title="title"
</hint>`;

const regexes = {
    coq: /```coq\n([\s\S]*?)\n```/g,
    math_display: /\$\$([\s\S]*?)\$\$/g,
    input_area: /<input-area>\n([\s\S]*?)\n<\/input-area>/g,
    hint: /<hint title="([\s\S]*?)">\n([\s\S]*?)\n<\/hint>/g,
    coqdoc: /\(\*\* ([\s\S]*?) \*\)/g
}

/*  order:
-> input-area / hint
--> parse those
-> math_display / coq / markdown
--> parse coq thingies.
*/

// const allInputAreas = Array.from(document.)
const allInputAreas = Array.from(document.matchAll(regexes.input_area));
for (const match of allInputAreas) {
    len = match.length;
    console.log(len, len > 1 ? match[1] : "no group");
}

const allHint = Array.from(document.matchAll(regexes.hint));
for (const match of allHint) {
    len = match.length;
    console.log(len, len > 1 ? match[1] : "no group", len > 2 ? match[2] : "no group");
    console.log("start", match.index, "end", match.index + match[0].length);
    console.log(document.substring(match.index, match.index + match[0].length));
}

// We can treat the content of the input area and the hints as a separate document. 
// Thus run the parser over these content blocks.

function handleDocument(docContent, checkForHintInput = true) {
    const nodes = [];
    if (checkForHintInput) {
        const allInputAreas = docContent.matchAll(regexes.input_area);
        const allHint = docContent.matchAll(regexes.hint);
        // The order of the children matters, keep that in mind.
        nodes.push(handleDocument(allInputAreas, false));
        nodes.push(handleDocument(allHint, false));
    } 

    const allMathDisplay = docContent.matchAll(regexes.math_display);
    const allCoq = docContent.matchAll(regexes.coq);
    // What remains is markdown content.
}