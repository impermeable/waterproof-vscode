import { EditorView } from "prosemirror-view";
import { SwitchableView } from "./switchable-view";
import { Node as PNode, Schema } from "prosemirror-model";
import { PluginKey } from "prosemirror-state";
import { toMathInline } from "../translation/toProsemirror/parser";

/**
 * MarkdownView class extends the SwitchableView class.
 * 
 * Used to edit and render markdown within the prosemirror editor.
 */
export class MarkdownView extends SwitchableView{
    
    constructor(
        getPos: (() => number | undefined), outerView: EditorView, 
        content: string, node: PNode, schema: Schema, 
        pluginKey: PluginKey, viewName: string
    ) {
        // Call the super constructor.
        super(getPos, outerView, content, node, schema, pluginKey, viewName, false);
    }

    preprocessContentForEditing(input: string): string {
        // We don't preprocess the content for editing.
        return input;
    }
    
    preprocessContentForRendering(input: string): string {
        // The only preprocessing we do here is converting $ dollar signs to math-inline nodes.
        return toMathInline("markdown", input);
    }

}