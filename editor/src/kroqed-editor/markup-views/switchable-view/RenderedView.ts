import { EditorView } from "prosemirror-view";
import { DOMParser } from "prosemirror-model";
import { mathPlugin } from "@benrbray/prosemirror-math";
import { EditorState, TextSelection } from "prosemirror-state";
import MarkdownIt from "markdown-it";
import { SwitchableView } from "./SwitchableView";
import { markdownRenderingSchema } from "./MarkdownSchema";
import { FileFormat } from "../../../../../shared";

export class RenderedView {
    public view: EditorView;
    private _outerView: EditorView;
    private _parent: SwitchableView;

    constructor(
        target: HTMLElement, 
        content: string, 
        outerView: EditorView, 
        parent: SwitchableView, 
        usingCoqdocSyntax: boolean,
        getPos: (() => number | undefined),
        
    ) {
        // Create a new MarkdownIt renderer with support for html (this allows 
        //  for the math-inline nodes to be passed through)
        const mdit = usingCoqdocSyntax 
            // Note: We disable 'code' (ie. four space) because this does not work nicely in the .v files.
            ? new MarkdownIt({html: true}).disable("code")
            : new MarkdownIt({html: true});
        // Render the markdown (converts it into a HTML string)
        const mditOutput = mdit.render(content);
        // Create a container element.
        const holder = document.createElement("div");
        this._outerView = outerView;
        this._parent = parent;
        // Set the holder innerHTML to the rendered markdown this way we can parse it to prosemirror.
        holder.innerHTML = mditOutput;
        // Create a prosemirror view with the math plugin enabled
        const view = new EditorView(target, {
            state: EditorState.create({
                doc: DOMParser.fromSchema(markdownRenderingSchema).parse(holder),
                schema: markdownRenderingSchema,
                plugins: [
                    mathPlugin, 
                ]
            }),
            // This view is not editable
            editable: (state) => { return false; }
        });
        // Save the view.
        this.view = view;
    }

    setSelection(anchor: number, head: number, root: Document | ShadowRoot) {
        this.view.focus();
        const $anchor = this.view.state.doc.resolve(anchor);
        const $head = this.view.state.doc.resolve(head);
        this._parent.updating = true;
        // Set the inner prosemirror selection by dispatching a new setSelection transaction.
        this.view.dispatch(this.view.state.tr.setSelection(new TextSelection($anchor, $head)));
        this._parent.updating = false;
    }

    update() {
		return true;   
    }

    focus() { this.view.focus() }
    destroy() { this.view.destroy() }
}
