import { PluginKey } from "prosemirror-state";
import { SwitchableView } from "./switchable-view";
import { EditorView } from "prosemirror-view";
import { Node as PNode, Schema } from "prosemirror-model";
import { translateCoqDoc, toMathInline } from "../translation/toProsemirror/parser";

/**
 * CoqdocView class extends the SwitchableView class.
 * 
 * Used to edit and render coqdoc syntax within the prosemirror editor.
 */
export class CoqdocView extends SwitchableView {

    constructor(
        getPos: (() => number | undefined), outerView: EditorView, 
        content: string, node: PNode, schema: Schema, 
        pluginKey: PluginKey, viewName: string
    ) {
        // Call the super constructor.
        super(getPos, outerView, content, node, schema, pluginKey, viewName);
    }

    preprocessContentForEditing(input: string): string {
        // We don't preprocess the input content for editing.
        return input;
    }
    preprocessContentForRendering(input: string): string {
        // We convert the coqdoc to markdown using a custom translator (`translationToMarkdown.ts`)
        // and convert the %'s to math-inline nodes.
        return toMathInline("coqdoc", translateCoqDoc(input));
    }
}