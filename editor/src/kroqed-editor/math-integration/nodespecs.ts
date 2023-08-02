import { NodeSpec } from "prosemirror-model"

/* 
	New schema specs for math-inline and math-display nodes (prosemirror-math)
	See: https://github.com/benrbray/prosemirror-math#schema
*/

// Schema spec for math inline nodes.
export const mathInlineSpec: NodeSpec = {
	group: "inline math",
	content: "text*",
	inline: true,
	atom: true,
	toDOM: () => ["math-inline", { class: "math-node" }, 0],
	parseDOM: [{
		tag: "math-inline"
	}]
}

// Schema spec for math display block nodes.
export const mathDisplaySpec: NodeSpec = {
	group: "block math",
	content: "text*",
	atom: true,
	code: true,
	toDOM: () => ["math-display", { class: "math-node" }, 0],
	parseDOM: [{
		tag: "math-display"
	}]
}