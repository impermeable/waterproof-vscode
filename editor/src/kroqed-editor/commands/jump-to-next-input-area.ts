import { Command, EditorState, NodeSelection, TextSelection, Transaction } from "prosemirror-state";
import { Node as PNode } from "prosemirror-model";
import { COQ_CODE_PLUGIN_KEY } from "../codeview/coqcodeplugin";

export function jumpToNextInputArea(): Command {
    return (state: EditorState, dispatch?: (tr: Transaction) => void): boolean => {
        if (!dispatch) return true;
        const inputAreas: Array<number> = [];
        state.doc.descendants((node, pos) => {
            if (node.type.name === "input") inputAreas.push(pos);
            return false;
        });
        console.log(inputAreas);
        const {from} = state.selection;
        console.log(from);
        const filtered = inputAreas.filter((value) => {return value > from});
        console.log(filtered);
        if (filtered.length > 0) {
            console.log("found", filtered[0]);
            const tr = state.tr;
            const posResolved = state.doc.resolve(filtered[0] + 3);
            tr.setSelection(new TextSelection(posResolved, posResolved));
            tr.scrollIntoView();
            dispatch(tr);
        }
        return true;
    }
}

export function printSelection(): Command {
    return (state: EditorState, dispatch?: (tr: Transaction) => void): boolean => {
        if(dispatch) console.log(state.selection); 
        return true;
    }
}