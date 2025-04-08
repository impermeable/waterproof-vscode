import {Tree} from "./Tree"
import { NodeType } from "prosemirror-model";

/**
 * We will preface this class with saying that this is most probably not 'the' smart approach. In fact,
 * it could possibly be simpler to do all this with the EditorState document node (textContent attribute).
 * However, we had thought this approach would be somewhat viable and nice for large documents, as you are not
 * sending the entire doc back and forth, but it comes at the cost of complexity.
 * 
 * This class is responsible for keeping track of the mapping between the prosemirror state and the vscode Text
 * Document model
 */
export class TextDocMappingNew {
    /** This stores the String cells of the entire document */
    private tree: Tree<number>
    /** The version of the underlying textDocument */
    private _version: number;

    /** The different possible HTMLtags in kroqed-schema */
    private static types: Set<string> = new Set<string>([
        "markdown",
        "input-area",
        "coqblock",
        "coqcode",
        "coqdoc",
        "math-display",
        "hint",
        "coqdown",
    ]);

    /** 
     * Constructs a prosemirror view vsode mapping for the inputted prosemirror html elem
     * 
     * @param inputBlocks a string contatining the prosemirror content html elem
     */
    constructor(inputBlocks: any, versionNum: number) {
        this._version = versionNum;
        this.tree = new Tree;
        this.initialize(inputBlocks);
    }
    //// The getters of this class

    /**
     * Returns the mapping to preserve integrity
     */
    public getMapping() {
        return this.tree
    }

    /**
     * Get the version of the underlying text document
     */
    public get version() {
        return this._version;
    }

    /** Returns the vscode document model index of prosemirror index */
    public findPosition(index: number) {
        
    }

    /** Returns the prosemirror index of vscode document model index */
    public findInvPosition(index: number) {
        
    }

    //// The methods used to manage the mapping

    /**
     * Initializes the mapping according to the inputed html content elem
     * 
     * @param inputString the string of the html elem
     */
    private initialize(inputBlocks: any) : void {
        let inner_constant = inputBlocks.content.content
        // console.log(inner_constant)
        console.log(inner_constant[0].content)
        this.printAllNodes(inner_constant[0].content)
        // console.log(inner_constant[0].content.content[0].type.name)

        // Remove this fragment layer
        let first_childs = new Array
        console.log(inner_constant)
        inner_constant[0].content.forEach((child: any) => {
            console.log(child)
            first_childs.push(child)
        });
        inner_constant.content = first_childs
        console.log(inner_constant)
        this.printAllNodes(inner_constant[0])

    }

    private printAllNodes(node: any, depth: number = 0): void {
        console.log(`${'  '.repeat(depth)}- ${node.type.name}`);
        node.content.forEach((child: any) => this.printAllNodes(child, depth + 1));
    }
    
}