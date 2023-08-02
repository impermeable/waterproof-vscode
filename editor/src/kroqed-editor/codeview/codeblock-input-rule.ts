import { InputRule } from "prosemirror-inputrules";
import { NodeType } from "prosemirror-model";

// user has to type '!coq' followed by a whitespace character.
export const codeblockInputRuleRegExp: RegExp = /!coq\s+$/i;


// adepted from prosemirror math.
export function makeCodeBlockInputRule(nodeType: NodeType) {
	return new InputRule(codeblockInputRuleRegExp, (state, match, start, end) => {
		let _start = state.doc.resolve(start);
		let index = _start.index();
		let _end = state.doc.resolve(end);
		
		// check if the replacement is valid
		if (!_start.parent.canReplaceWith(index, _end.index(), nodeType)) {
			return null;
		}

		// perform replacement
		return state.tr.replaceRangeWith(
			start,
			end,
			nodeType.create({}, nodeType.schema.text("This is a new coq cell"))
		);
	});
}
