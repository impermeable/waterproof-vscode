import { Tree, TreeNode } from "./Tree";
import { Step, ReplaceStep, ReplaceAroundStep, typeguards, Node, TagConfiguration, WaterproofMapping, MappingError, WaterproofSchema, Serializers } from "@impermeable/waterproof-editor";
import { TextUpdate } from "./textUpdate";
import { NodeUpdate } from "./nodeUpdate";
import { ParsedStep } from "./types";
import { Block, DocChange, WrappingDocChange } from "@impermeable/waterproof-editor";

/**
 * This class is responsible for keeping track of the mapping between the prosemirror state and the vscode Text
 * Document model
 */
export class TextDocMappingNew implements WaterproofMapping {
    /** This stores the String cells of the entire document */
    private tree: Tree;
    /** The version of the underlying textDocument */
    private _version: number;

    private readonly nodeUpdate: NodeUpdate;
    private readonly textUpdate: TextUpdate;

    /**
     * Constructs a prosemirror view vscode mapping for the inputted prosemirror html element
     *
     * @param inputBlocks a string containing the prosemirror content html element
     */
    constructor(inputBlocks: Block[], versionNum: number, tMap: TagConfiguration, serializers: Serializers) {
        this.textUpdate = new TextUpdate();
        this.nodeUpdate = new NodeUpdate(tMap, serializers);
        this._version = versionNum;
        this.tree = new Tree();
        this.initialize(inputBlocks);
        console.log(inputBlocks);
        console.log("MAPPED TREE", JSON.stringify(this.tree));
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
        const correctNode: TreeNode | null = this.tree.findNodeByProsemirrorPosition(index);
        if (correctNode === null) throw new MappingError(" [findPosition] The vscode document model index could not be found ");
        return (index - correctNode.prosemirrorStart) + correctNode.innerRange.from;
    }

    /** Returns the prosemirror index of vscode document model index */
    public findInvPosition(index: number) {
        const correctNode: TreeNode | null = this.tree.findNodeByOriginalPosition(index);
        if (correctNode === null) throw new MappingError(" [findInvPosition] The vscode document model index could not be found ");
        return (index - correctNode.innerRange.from) + correctNode.prosemirrorStart;
    }

    private inStringCell(step: ReplaceStep | ReplaceAroundStep): boolean {
        const correctNode: TreeNode | null = this.tree.findNodeByProsemirrorPosition(step.from);
        return correctNode !== null && step.to <= correctNode.prosemirrorEnd;
    }

    public update(step: Step, doc: Node): DocChange | WrappingDocChange {
        console.log("STEP IN UPDATE", step)
        if (!(step instanceof ReplaceStep || step instanceof ReplaceAroundStep))
            throw new MappingError("Step update (in textDocMapping) should not be called with a non document changing step");

        /** Check whether the edit is a text edit */       
        let isText: boolean;
        if (step.slice.content.firstChild?.type === WaterproofSchema.nodes.text) {
            // Short circuit when the content is a text node. This is the case for simple text insertions
            // This is probably the most used path
            isText = true;
        } else {
            // TODO: Figure out if this takes a lot of computation and whether we can do this more efficiently.
            // A textual deletion has no content, but so do node deletions. We differentiate between them by
            // checking what the parent node of the from position is. 
            const parentNodeType = doc.resolve(step.from).parent.type;
            isText = (step.slice.content.childCount === 0 &&
                (parentNodeType === WaterproofSchema.nodes.markdown ||
                    parentNodeType === WaterproofSchema.nodes.code ||
                    parentNodeType === WaterproofSchema.nodes.math_display));
        }

        let result: ParsedStep;

        /** Parse the step into a text document change */
        if (step instanceof ReplaceStep && isText) result = this.textUpdate.textUpdate(step, this);
        else result = this.nodeUpdate.nodeUpdate(step, this);

        this.tree = result.newTree

        if ('finalText' in result.result) {
            if (this.checkDocChange(result.result)) this._version++;
        } else {
            if (this.checkDocChange(result.result.firstEdit) || this.checkDocChange(result.result.secondEdit)) this._version++;
        }

        return result.result;
    }

    /**
     * This checks if the doc change actually changed the document, since vscode
     * does not register empty changes 
     */
    private checkDocChange(change: DocChange): boolean {
        if (change.endInFile === change.startInFile && change.finalText.length == 0) return false;
        return true;
    }

    //// The methods used to manage the mapping

    /**
     * Initializes the mapping according to the inputted HTML content element
     *
     * @param inputBlocks the structure representing the inputted HTML content
     */
    private initialize(inputBlocks: Block[]): void {
        this.mapToTree(inputBlocks);
    }

    private mapToTree(blocks: Block[]): void {
        // Create a root node with dummy values

        const root = new TreeNode(
            "", // type
            { from: 0, to: blocks.at(-1)!.range.to }, // originalStart
            { from: 0, to: blocks.at(-1)!.range.to }, // originalEnd
            "", // title
            0, // prosemirrorStart
            0, // prosemirrorEnd
            "" // stringContent
        );

        function buildSubtree(blocks: Block[]): TreeNode[] {
            return blocks.map(block => {

                const title = typeguards.isHintBlock(block) ? block.title : "";

                const node = new TreeNode(
                    block.type,
                    block.innerRange,
                    block.range,
                    title,
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
        this.computeProsemirrorOffsets(this.tree.root);
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
        currentOffset: number = 0,
        level: number = 0
    ): number {
        if (!node) return currentOffset;
        
        let offset = currentOffset;

        if (node.type === "newline") {
            node.prosemirrorStart = offset + 1;
            node.prosemirrorEnd = offset + 2;
            return offset;
        }

        // Add start tag and +1 for going one level deeper
        if (node !== this.tree.root) {
            offset += 1;
        }

        // Record the ProseMirror start after entering this node
        node.prosemirrorStart = offset;

        if (node.children.length === 0) {
            // Leaf: add stringContent + end tag + +1 for exiting level
            offset += node.stringContent.length;
        } else {
            // Non-leaf: handle children and end tag
            for (let i = 0; i < node.children.length; i++) {
                if (i > 0) {
                    offset += 1; // +1 between siblings
                }
                offset = this.computeProsemirrorOffsets(
                    node.children[i],
                    offset,
                    level + 1
                );
            }
            // After all children: add end tag
            offset += 1;
        }

        node.prosemirrorEnd = offset;

        return offset;
    }

}
