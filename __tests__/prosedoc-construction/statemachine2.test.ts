import { DocumentParser } from "../../editor/src/document-construction/statemachine"


// const doc = `Here is some introductory text.
// \`\`\`python
// def example_function():
//     return "Hello, World!"
// \`\`\`
// <hint title="Important Hint">
// This is a hint block with some **markdown** content.

// \`\`\`python
// # Nested code block inside hint
// print("This is a nested code block")
// \`\`\`
// More hint text.
// </hint>Some concluding text.
// $$
// E = mc^2
// $$`;

const doc = `# test
\`\`\`python
def example_function():
    return "Hello, World!"
\`\`\`
test
\`\`\`python
def example_function():
\`\`\`
<hint title="Important Hint">
This is a hint block with some **markdown** content.
</hint>`;

test("test", () => {
    const parser = new DocumentParser(doc, "python");
    console.log(parser.parse());
});