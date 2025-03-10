import { Decoration, EditorView, NodeView } from "prosemirror-view";
import { EditableView } from "./EditableView";
import { RenderedView } from "./RenderedView";
import { NodeSelection, PluginKey } from "prosemirror-state";
import { Node as PNode, Schema } from "prosemirror-model";

/**
 * Abstract class for a switchable view. 
 * Switchable views allow for editing and rendering. 
 */
export abstract class SwitchableView implements NodeView {
    /** The DOM for this nodeview. */
    dom: HTMLElement;
    /** The currently active view. */
    private view: EditableView | RenderedView;
    /** Whether we are in rendered mode */
    private inRenderMode: boolean = true;
    /** The place to insert the views into */
    private _place: HTMLElement;
    /** The outer prosemirror editor */
    private _outerView: EditorView;
    /** The node that is passed when constructing the NodeView */
    private _node: PNode;

    /** Represents whether the view is currently updating */
    private _updating : boolean;
    private _getPos: (() => number | undefined);
    private _outerSchema;
    
    
    private _viewName: string;
    private _pluginKey: PluginKey;

    private _emptyClassName: string;
    private _viewClassName: string;
    private _editorClassName: string;
    private _renderedClassName: string;

    private _usingCoqdocSyntax: boolean;

    public get content() {
        return this._node.textContent;
    }

    constructor(
        getPos: (() => number | undefined), outerView: EditorView, 
        content: string, node: PNode, schema: Schema, 
        pluginKey: PluginKey, viewName: string,
        usingCoqdocSyntax: boolean
    ) {
        // Store parameters
        this._node = node;
        this._getPos = getPos;
        this._outerView = outerView;
        this._outerSchema = schema;
        this._viewName = viewName;
        this._pluginKey = pluginKey;
        this._usingCoqdocSyntax = usingCoqdocSyntax;
        
        // Set-up dom related things.
        const container = document.createElement("div");
        this._place = document.createElement("div");
        this.dom = container;

        // Create class names
        this._viewClassName = `${viewName}-view`;
        this._emptyClassName = `${this._viewClassName}-empty`;
        this._renderedClassName = `${this._viewClassName}-rendered`;
        this._editorClassName = `${this._viewClassName}-editor`;

        this.dom.appendChild(this._place);

        this.dom.classList.add(this._viewClassName);

        // If the content is an empty string add an empty class to the dom element.
        if (content === "") {
            this.dom.classList.add(this._emptyClassName);
        }
        // We start with a rendered markdown view.
        const processedContent = this.preprocessContentForRendering(this._node.textContent);
        this.view = new RenderedView(this._place, processedContent, this._outerView, this, usingCoqdocSyntax, this._getPos);

        // eventHandler for the onclick event. 
        // Creates a new node selection that selects 'this' node. 
        const eventHandler = () => {
            const tr = outerView.state.tr;
            const pos = getPos();
            if (pos === undefined) {
                console.error("why pos undefined?!");
                return;
            }
            const nodeSel = new NodeSelection(outerView.state.doc.resolve(pos));
            tr.setSelection(nodeSel);
            outerView.dispatch(tr);
        };

        // Add handlers
        this.dom.addEventListener("click", eventHandler);
        this._place.addEventListener("click", eventHandler);
        this._updating = false;
    }

    /**
     * Returns whether this view is currently in the updating state.
     */
    public get isUpdating() {
        return this._updating;
    }

    /**
     * Overwrite the updating state of this node.
     */
    public set updating(update: boolean) {
        this._updating = update;
    }

    /**
     * Switch to the rendered view.
     * This destroys the view currently in place and then adds a new rendered view.
     */ 
    makeRenderedView() {
        this.view.destroy();
        const inputContent = this.preprocessContentForRendering(this._node.textContent);
        if (inputContent === "") {
            // If it is empty we add the empty class
            this.dom.classList.add(this._emptyClassName);
        }
        // Add/ remove classes for styling.
        this.dom.classList.remove(this._editorClassName);
        this.dom.classList.add(this._renderedClassName);
        // Create the new rendered view and set it as the current view
        this.view = new RenderedView(this._place, inputContent, this._outerView, this, this._usingCoqdocSyntax, this._getPos);
    }

    /**
     * Switch to the editable view.
     * This destroys the view currently in place and then adds a new editable view.
     */
    makeEditableView() {
        this.view.destroy();
        this.dom.classList.remove(this._emptyClassName);
        // Add/ Remove classes for styling.
        this.dom.classList.remove(this._renderedClassName);
        this.dom.classList.add(this._editorClassName);
        // Create a new editable view and it as the current view.
        this.view = new EditableView(this._node, this._outerView, this._outerSchema, this._getPos, this._place, this, this._pluginKey);
    }

    // Abstract functions that can be overridden to preprocess the content before switching views.
    abstract preprocessContentForEditing(input: string): string;
    abstract preprocessContentForRendering(input: string): string;

    update(node: PNode, decorations: readonly Decoration[]) {
        if (!node.sameMarkup(this._node)) return false;
        this._node = node;
        if (this.view instanceof RenderedView) this.makeEditableView();
        return this.view.update(node,decorations);
    }

    selectNode() {
        // Add default prosemirror style for selected nodes.
        this.dom.classList.add("ProseMirror-selectednode");
        // Only allow editing if outer view is not locked
        if (!this._outerView.editable) return; 
        if (!this.inRenderMode) return;
        // Switch to editable view if we select this node.
        this.makeEditableView();
        this.inRenderMode = false;
    }

    deselectNode() {
        this.dom.classList.remove("ProseMirror-selectednode");
        if (this.inRenderMode) return;
        // This is were we render the markdown, since the user has left this cell.
        this.makeRenderedView();
        this.inRenderMode = true;
    }
    
    setSelection(anchor: number, head: number, root: Document | ShadowRoot) {
        // Set the selection in the inner view.
        this.view.setSelection(anchor, head, root);
    }

    stopEvent(event: Event) {
        const { target } = event;
        if (event instanceof KeyboardEvent && event.ctrlKey) {
            return false;
        }
        return (this.dom !== undefined && target !== undefined && this.dom.contains(target as HTMLElement));
    }

    ignoreMutation() { return true; }
    
    destroy() {
        this.dom.remove();
    }
}