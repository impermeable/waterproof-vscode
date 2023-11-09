import { cursorGroupLeft, selectGroupLeft, cursorLineBoundaryLeft, selectLineBoundaryLeft, cursorGroupRight, selectGroupRight, cursorLineBoundaryRight, selectLineBoundaryRight, cursorDocStart, selectDocStart, cursorPageUp, selectPageUp, cursorDocEnd, selectDocEnd, cursorPageDown, selectPageDown, cursorLineBoundaryBackward, selectLineBoundaryBackward, cursorLineBoundaryForward, selectLineBoundaryForward, insertNewlineAndIndent, deleteCharBackward, deleteCharForward, deleteGroupBackward, deleteGroupForward, cursorCharLeft, cursorCharRight, cursorLineDown, cursorLineUp, selectCharLeft, selectCharRight, selectLineDown, selectLineUp, selectAll } from "@codemirror/commands";
import { KeyBinding } from "@codemirror/view";

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
]