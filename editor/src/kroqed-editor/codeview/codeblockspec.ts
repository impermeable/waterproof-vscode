import { NodeSpec } from "prosemirror-model";

// Custom NodeSpec for a codeblock node. 
export const codeblockSpec: NodeSpec = {
	group: "inline", // Considered as inline element
	content: "text*",// content is of type text
	inline: true,
	code: true,
	atom: true, // doesn't have directly editable content (content is edited through codemirror)
	toDOM: () => ["codeblock", 0], // <codeblock></codeblock> cells
	parseDOM: [{tag: "codeblock"}]
};