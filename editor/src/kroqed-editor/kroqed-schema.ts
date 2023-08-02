import { Node as PNode, Schema } from "prosemirror-model";
import { QedStatus } from "../../../shared";

const cell = "(markdown | hint | coqblock | input | math_display)";
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
 * see [notes](notes.txt)
 */
export const TheSchema: Schema = new Schema({
	nodes: {
		doc: {
			content: `${cell}*`
		},

		/////// MARKDOWN ////////
		//#region Markdown
		markdown: {
			block: true,
			content: "text*",
			parseDOM: [{tag: "markdown", preserveWhitespace: "full"}],
			atom: true,
			toDOM(node) {
				return ["markdown", 0];
			},
		},

		text: {
			group: "inline"
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
			parseDOM: [{tag: "hint", getAttrs(dom) {
				return {
					title: (dom as HTMLElement).getAttribute("title") ?? "💡 Hint"
				}
			}}],
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
			parseDOM: [{tag: "input-area", getAttrs(dom) {
			let statusAttr = (dom as HTMLElement).getAttribute("status");
			return {
				status: statusAttr && statusAttr in QedStatus && statusAttr !== "invalid" ? statusAttr : null
			};
			}}],
			toDOM: (node: PNode) => {
			return ["input-area", {class: "inputarea"}, 0];
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
			},
			parseDOM: [{tag: "coqblock", getAttrs(dom) {
				return {
					prePreWhite: (dom as HTMLElement).getAttribute("prePreWhite") ?? "newLine",
					prePostWhite: (dom as HTMLElement).getAttribute("prePostWhite") ?? "newLine",
					postPreWhite: (dom as HTMLElement).getAttribute("postPreWhite") ?? "newLine",
					postPostWhite: (dom as HTMLElement).getAttribute("postPostWhite") ?? "newLine"
				}
			}}]
		},

		coqdoc: {
			content: "(math_display | coqdown)*",
			attrs: {
				preWhite:{default:"newLine"},
				postWhite:{default:"newLine"}
			},
			toDOM: () => {
				return ["coqdoc", 0];
			},
			parseDOM: [{tag: "coqdoc", getAttrs(dom) {
				return {
					preWhite: (dom as HTMLElement).getAttribute("preWhite") ?? "newLine",
					postWhite: (dom as HTMLElement).getAttribute("postWhite") ?? "newLine"
				}
			}}]
		},

		coqdown: {
			content: "text*",
			block: true,
			atom: true,
			toDOM: () => {
				return ["coqdown", 0];
			},
			parseDOM: [{tag: "coqdown", preserveWhitespace: "full"}]
		},

		coqcode: {
			content: "text*",// content is of type text
			code: true,
			atom: true, // doesn't have directly editable content (content is edited through codemirror)
			parseDOM: [{tag: "coqcode", preserveWhitespace: "full"}],
			toDOM(node) { return ["coqcode", node.attrs, 0] } // <coqcode></coqcode> cells
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
			parseDOM: [{
				tag: "math-display", preserveWhitespace: "full"
			}]
		},
		//#endregion
	},
	marks: {
		em: {
		  parseDOM: [{tag: "i"}, {tag: "em"}],
		  toDOM() { return ["em"] }
		},

		strong: {
		  parseDOM: [{tag: "b"}, {tag: "strong"}],
		  toDOM() { return ["strong"] }
		},

		link: {
		  attrs: {
			href: {},
			title: {default: null}
		  },
		  inclusive: false,
		  parseDOM: [{tag: "a[href]", getAttrs(dom) {
			return {href: (dom as HTMLElement).getAttribute("href"), title: (dom as HTMLElement).getAttribute("title")}
		  }}],
		  toDOM(node) { return ["a", node.attrs] }
		},

		code: {
		  parseDOM: [{tag: "code"}],
		  toDOM() { return ["code"] }
		}
	}
});