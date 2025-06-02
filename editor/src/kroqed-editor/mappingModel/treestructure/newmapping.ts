import { Tree, TreeNode } from "./Tree";
import { Block } from "../../prosedoc-construction/blocks";

/**
 * This class is responsible for keeping track of the mapping between the prosemirror state and the vscode Text
 * Document model
 */
export class TextDocMappingNew {
    /** This stores the String cells of the entire document */
    private tree: Tree;
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

    /** This stores the characters that each 'starting' HTML tag represents in the original document */
    private startTag: Map<string, string> = new Map<string, string>([
        ["coqblock", "```coq"],
        ["coqdown", ""],
        ["math-display", "$"],
        ["input-area", "<input-area>"],
        ["markdown", ""],
        ["math_display", "$"],
        ["input", "<input-area>"],
        ["text", ""],
    ]);

    /** This stores the characters that each 'ending' HTML tag represents in the original document */
    private endTag: Map<string, string> = new Map<string, string>([
        ["coqblock", "```"],
        ["coqdown", ""],
        ["math-display", "$"],
        ["input-area", "</input-area>"],
        ["markdown", ""],
        ["hint", "</hint>"],
        ["math_display", "$"],
        ["input", "</input-area>"],
        ["text", ""],
    ]);

    /**
     * Constructs a prosemirror view vscode mapping for the inputted prosemirror html element
     *
     * @param inputBlocks a string containing the prosemirror content html element
     */
    constructor(inputBlocks: any, versionNum: number) {
        this._version = versionNum;
        this.tree = new Tree();
        this.initialize(inputBlocks);
    }

    //// The getters of this class

    /**
     * Returns the mapping to preserve integrity
     */
    public getMapping() {
        return this.tree;
    }

    /**
     * Get the version of the underlying text document
     */
    public get version() {
        return this._version;
    }

    /** Returns the vscode document model index of prosemirror index */
    public findPosition(index: number) {
        // Implement as needed
    }

    /** Returns the prosemirror index of vscode document model index */
    public findInvPosition(index: number) {
        // Implement as needed
    }

    //// The methods used to manage the mapping

    /**
     * Initializes the mapping according to the inputted HTML content element
     *
     * @param inputBlocks the structure representing the inputted HTML content
     */
    private initialize(inputBlocks: any): void {
        this.mapToTree(inputBlocks);
        console.log(this.tree); // For debugging
    }

    private printAllNodes(node: any, depth: number = 0): void {
        console.log(`${'  '.repeat(depth)}- ${node.type}`);
        console.log(node);
        node.content.forEach((child: any) => {
            this.printAllNodes(child, depth + 1);
        });
    }

    private mapToTree(blocks: Block[]): void {
        // Create a root node with dummy values
        const root = new TreeNode(
            "", // type
            0, // originalStart
            0, // originalEnd
            0, // prosemirrorStart
            0, // prosemirrorEnd
            "" // stringContent
        );

    function buildSubtree(blocks: Block[]): TreeNode[] {
        return blocks.map(block => {
            const node = new TreeNode(
                block.type,
                block.innerRange.from,
                block.innerRange.to,
                0, // prosemirrorStart (to be calculated later)
                0, // prosemirrorEnd (to be calculated later)
                block.stringContent // always keep the stringContent
            );

            if (block.innerBlocks && block.innerBlocks.length > 0) {
                const children = buildSubtree(block.innerBlocks);
                children.forEach(child => node.addChild(child));
            }

            return node;
        });
    }


        const topLevelNodes = buildSubtree(blocks);
        topLevelNodes.forEach(child => root.addChild(child));

        // Set the tree root after mapping
        this.tree.root = root;

        console.log(this.tree);

        // Now compute the ProseMirror offsets after creating the tree structure
        this.computeProsemirrorOffsets(this.tree.root, this.startTag, this.endTag);
    }

    /**
     * Recursively computes the prosemirrorStart and prosemirrorEnd offsets for each node.
     * 
     * @param node The current node to compute the offsets for.
     * @param startTagMap The start tag mapping for each block type.
     * @param endTagMap The end tag mapping for each block type.
     * @param currentOffset The current offset from where the computation should begin.
     * @param level The current depth level in the tree (used for adjusting offsets).
     * @returns The updated offset after computing the current node.
     */
    private computeProsemirrorOffsets(
        node: TreeNode | null,
        startTagMap: Map<string, string>,
        endTagMap: Map<string, string>,
        currentOffset: number = 0,
        level: number = 0
    ): number {
        if (!node) return currentOffset;

        const startTagStr = startTagMap.get(node.type) ?? "";
        const endTagStr = endTagMap.get(node.type) ?? "";

        let offset = currentOffset;

        // Add start tag and +1 for going one level deeper
        if (node !== this.tree.root) {
            offset += startTagStr.length + 1;
        }

        // Record the ProseMirror start after entering this node
        node.prosemirrorStart = offset;

        if (node.children.length === 0) {
            // Leaf: add stringContent + end tag + +1 for exiting level
            console.log("string_content")
            console.log(node)
            offset += node.stringContent.length + endTagStr.length;
        } else {
            // Non-leaf: handle children and end tag
            for (let i = 0; i < node.children.length; i++) {
                if (i > 0) {
                    offset += 1; // +1 between siblings
                }
                offset = this.computeProsemirrorOffsets(
                    node.children[i],
                    startTagMap,
                    endTagMap,
                    offset,
                    level + 1
                );
            }
            // After all children: add end tag
            offset += endTagStr.length + 1;
        }

        console.log(offset)
        node.prosemirrorEnd = offset;

        return offset;
    }

    // Helper to get full content for a node (recursive)
    private getFullNodeContent(
        node: TreeNode,
        startTagMap: Map<string, string>,
        endTagMap: Map<string, string>
    ): string {
        if (node.children.length === 0) {
            const start = startTagMap.get(node.type) ?? "";
            const end = endTagMap.get(node.type) ?? "";
            return `${start}${node.stringContent}${end}`;
        }

        // For non-leaf nodes, return the built content (without stringContent for non-leaf nodes)
        return "";
    }
}
