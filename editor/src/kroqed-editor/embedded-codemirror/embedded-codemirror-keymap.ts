import { cursorGroupLeft, selectGroupLeft, cursorLineBoundaryLeft, selectLineBoundaryLeft, cursorGroupRight, selectGroupRight, cursorLineBoundaryRight, selectLineBoundaryRight, cursorDocStart, selectDocStart, cursorPageUp, selectPageUp, cursorDocEnd, selectDocEnd, cursorPageDown, selectPageDown, cursorLineBoundaryBackward, selectLineBoundaryBackward, cursorLineBoundaryForward, selectLineBoundaryForward, insertNewlineAndIndent, deleteCharBackward, deleteCharForward, deleteGroupBackward, deleteGroupForward, cursorCharLeft, cursorCharRight, cursorLineDown, cursorLineUp, selectCharLeft, selectCharRight, selectLineDown, selectLineUp, selectAll,indentWithTab, indentLess, indentMore,  } from "@codemirror/commands";
import { KeyBinding } from "@codemirror/view";
import { acceptCompletion } from "@codemirror/autocomplete";
import { indentUnit } from "@codemirror/language";
import {EditorState, StateCommand, SelectionRange, ChangeSpec, Line, EditorSelection} from "@codemirror/state"
import { EditorView as CodeMirror } from "@codemirror/view";
import { EditorView } from "prosemirror-view";
/**
 * Filtered set of keybindings taken from
 * https://github.com/codemirror/commands/blob/e27916c9b09d2cedd7e0c9770bff04eeb3696e69/src/commands.ts#L878
 */

export const keybindings: KeyBinding[] = [
    { key: "Mod-A", run: selectAll, preventDefault: true },
    { key: "ArrowLeft", run: cursorCharLeft, shift: selectCharLeft, preventDefault: true },
    { key: "ArrowRight", run: cursorCharRight, shift: selectCharRight, preventDefault: true },
    { key: "ArrowUp", run: cursorLineUp, shift: selectLineUp, preventDefault: true },
    { key: "ArrowDown", run: cursorLineDown, shift: selectLineDown, preventDefault: true },

    { key: "Mod-ArrowLeft", mac: "Alt-ArrowLeft", run: cursorGroupLeft, shift: selectGroupLeft, preventDefault: true },
    { mac: "Cmd-ArrowLeft", run: cursorLineBoundaryLeft, shift: selectLineBoundaryLeft, preventDefault: true },

    { key: "Mod-ArrowRight", mac: "Alt-ArrowRight", run: cursorGroupRight, shift: selectGroupRight, preventDefault: true },
    { mac: "Cmd-ArrowRight", run: cursorLineBoundaryRight, shift: selectLineBoundaryRight, preventDefault: true },

    { key: "PageUp", run: cursorPageUp, shift: selectPageUp },
    { key: "PageDown", run: cursorPageDown, shift: selectPageDown },

    { key: "Home", run: cursorLineBoundaryBackward, shift: selectLineBoundaryBackward, preventDefault: true },
    { key: "Mod-Home", run: cursorDocStart, shift: selectDocStart },

    { key: "End", run: cursorLineBoundaryForward, shift: selectLineBoundaryForward, preventDefault: true },
    { key: "Mod-End", run: cursorDocEnd, shift: selectDocEnd },

    { key: "Enter", run: insertNewlineAndIndent },

    { key: "Backspace", run: deleteCharBackward, shift: deleteCharBackward },
    { key: "Delete", run: deleteCharForward },
    { key: "Mod-Backspace", mac: "Alt-Backspace", run: deleteGroupBackward },
    { key: "Mod-Delete", mac: "Alt-Delete", run: deleteGroupForward },

    { key: "Mod-Delete", mac: "Alt-Delete", run: deleteGroupForward },
    {key: "Tab", run: customTab, preventDefault: false},
]



function changeBySelectedLineCustom(state: EditorState, f: (line: Line, changes: ChangeSpec[], range: SelectionRange) => void) {
	let atLine = 2
	return state.changeByRange(range => {
	  let changes: ChangeSpec[] = []
	  for (let pos = range.from; pos <= range.to;) {
		let line = state.doc.lineAt(pos)
		if (line.number < atLine && (range.empty || range.to > line.from)) {
		  f(line, changes, range)
		  atLine = line.number
		}
		pos = line.to + 1
	  }
	  let changeSet = state.changes(changes)
	  return {changes,
			  range: EditorSelection.range(changeSet.mapPos(range.anchor, 1), changeSet.mapPos(range.head, 1))}
	})
  }
export const indentMoreCustom: StateCommand = ({state, dispatch}) => {
	if (state.readOnly) return false
	dispatch(state.update(changeBySelectedLineCustom(state, (line, changes) => {
	  changes.push({from: line.from, insert: state.facet(indentUnit)})
	}), {userEvent: "input.indent"}))
	return true
  }
function customTab(view: CodeMirror){	
	if (acceptCompletion(view)) {
        return true; 
    }
	return indentMoreCustom(view)

}