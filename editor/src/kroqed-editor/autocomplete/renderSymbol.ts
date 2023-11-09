import { Completion } from "@codemirror/autocomplete";
import { EditorState } from "@codemirror/state";

const render = (completion: Completion, state: EditorState): globalThis.Node | null => {
    // We only render an icon in the case that this is a symbol
    if (completion.type !== "symbol") return null;
    
    const div = document.createElement("div");
    // The type conversion here should be fine, since we 
    // store all the symbol completions in a JSON file anyway.
    div.innerText = completion.apply as string;
    div.classList.add("symbol-completion-icon");
    return div;
}

const position = 0;

export const renderIcon = {
    render,
    position
}