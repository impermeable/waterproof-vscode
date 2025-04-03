import { Node as PNode, Schema } from "prosemirror-model";

export const SchemaCell = {
	InputArea: "input",
	Markdown: "markdown",
	MathDisplay: "math_display",
	Code: "code"
} as const;

export type SchemaKeys = keyof typeof SchemaCell;
export type SchemaNames = typeof SchemaCell[SchemaKeys];

const cell = `(markdown | hint | coqblock | input | math_display)`;
const containercontent = "(markdown | coqblock | math_display)";
// const groupMarkdown = "markdowncontent";

/**
 * General schema obtained from `prosemirror-markdown`:
 * https://github.com/ProseMirror/prosemirror-markdown/blob/master/src/schema.ts
 *
 * Codeblock schema adapted from 'ProseMirror footnote example':
 * https://prosemirror.net/examples/footnote/
 *
 * math blocks obtained from `prosemirror-math`:
 * https://github.com/benrbray/prosemirror-math/blob/master/src/math-schema.ts
 *
 * see [notes](./notes.md)
 */
export const WaterproofSchema: Schema = new Schema({
	nodes: {
		doc: {
			content: `${cell}*`
		},

		text: {
			group: "inline"
		},

		/////// MARKDOWN ////////
		//#region Markdown
		markdown: {
			block: true,
			content: "text*",
			parseDOM: [{tag: "markdown", preserveWhitespace: "full"}],
			atom: true,
			toDOM: () => {
				return ["WaterproofMarkdown", 0];
			},
		},
		//#endregion

		/////// HINT //////
		//#region Hint
		hint: {
			content: `${containercontent}*`,
			attrs: {
				title: {default: "💡 Hint"},
				shown: {default: false}
			},
			toDOM(node: PNode) {
				return ["div", {class: "hint", shown: node.attrs.shown}, 0];
			}
		},
		//#endregion

		/////// Input Area //////
		//#region input
		input: {
			content: `${containercontent}*`,
			attrs: {
				status: {default: null}
			},
			toDOM: () => {
				return ["WaterproofInput", {class: "inputarea"}, 0];
			}
		},
		//#endregion

		////// Coqblock //////
		//#region Coq codeblock
		"coqblock": {
			content: `(coqdoc | coqcode)+`,
			attrs: {
				prePreWhite:{default:"newLine"},
				prePostWhite:{default:"newLine"},
				postPreWhite:{default:"newLine"},
				postPostWhite:{default:"newLine"}
			},
			toDOM: () => {
				return ["coqblock", 0];
			}
		},

		coqdoc: {
			content: "(math_display | coqdown)*",
			attrs: {
				preWhite:{default:"newLine"},
				postWhite:{default:"newLine"}
			},
			toDOM: () => {
				return ["coqdoc", 0];
			}
		},

		coqdown: {
			content: "text*",
			block: true,
			atom: true,
			toDOM: () => {
				return ["coqdown", 0];
			},
		},

		coqcode: {
			content: "text*",// content is of type text
			code: true,
			atom: true, // doesn't have directly editable content (content is edited through codemirror)
			toDOM(node) { return ["WaterproofCode", node.attrs, 0] } // <coqcode></coqcode> cells
		},
		//#endregion

		/////// MATH DISPLAY //////
		//#region math-display
		math_display: {
			group: "math",
			content: "text*",
			atom: true,
			code: true,
			toDOM(node) { return ["math-display", {...{ class: "math-node" }, ...node.attrs}, 0]; },
		},
		//#endregion
	},
	// marks: {
	// 	em: {
	// 	  toDOM() { return ["em"] }
	// 	},

	// 	strong: {
	// 	  toDOM() { return ["strong"] }
	// 	},

	// 	link: {
	// 	  attrs: {
	// 		href: {},
	// 		title: {default: null}
	// 	  },
	// 	  inclusive: false,
	// 	  toDOM(node) { return ["a", node.attrs] }
	// 	},

	// 	code: {
	// 	  toDOM() { return ["code"] }
	// 	}
	// }
});