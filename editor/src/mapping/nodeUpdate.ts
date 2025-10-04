import { ReplaceAroundStep, ReplaceStep, Node as PNode, WaterproofSchema, WrappingDocChange, NodeUpdateError, TagConfiguration, DocumentSerializer } from "@impermeable/waterproof-editor";
import { Tree, TreeNode } from "./Tree";
import { OperationType, ParsedStep } from "./types";
import { DocChange } from "@impermeable/waterproof-editor";
import { Mapping } from "./newmapping";
import { typeFromStep } from "./helper-functions";

export class NodeUpdate {
    // Store the tag configuration and serializer
    constructor (private tagConf: TagConfiguration, private serializer: DocumentSerializer) {} 

    // Utility to get the opening and closing tag for a given node type
    nodeNameToTagPair(nodeName: string, title: string = ""): [string, string] {
        switch (nodeName) {
            case "markdown":
                return [this.tagConf.markdown.openTag, this.tagConf.markdown.closeTag];
            case "code":
                return [this.tagConf.code.openTag, this.tagConf.code.closeTag];
            case "hint":
                return [this.tagConf.hint.openTag(title), this.tagConf.hint.closeTag];
            case "input":
                return [this.tagConf.input.openTag, this.tagConf.input.closeTag];
            case "math_display":
                return [this.tagConf.math.openTag, this.tagConf.math.closeTag];
            default:
                throw new NodeUpdateError(`Unsupported node type: ${nodeName}`);
        }
    }
    
    // Handle a node update step
    public nodeUpdate(step: ReplaceStep | ReplaceAroundStep, mapping: Mapping) : ParsedStep {
        console.log("IN NODE UPDATE", step, mapping.getMapping());

        let parsedStep;
        if (step instanceof ReplaceStep) {
            // The step is a ReplaceStep
            parsedStep = this.doReplaceStep(step, mapping);
        } else {
            // The step is a ReplaceAroundStep (wrapping or unwrapping of nodes)
            parsedStep = this.doReplaceAroundStep(step, mapping);
        }

        console.log("TREEEE", JSON.stringify(parsedStep.newTree));
        return parsedStep;
    }

    doReplaceStep(step: ReplaceStep, mapping: Mapping): ParsedStep {
        // Determine operation type
        const type = typeFromStep(step);
        console.log("In doReplaceStep, operation type:", type);
        switch (type) {
            case OperationType.insert:
                return this.replaceInsert(step, mapping.getMapping());
            case OperationType.delete:
                return this.replaceDelete(step, mapping.getMapping());
            case OperationType.replace:
                throw new NodeUpdateError(" We do not support ReplaceSteps that replace nodes with other nodes (textual replaces are handled in the textUpdate module) ");
        }
    }

    doReplaceAroundStep(step: ReplaceAroundStep, mapping: Mapping): ParsedStep {
        // Determine operation type
        const type = typeFromStep(step);
        switch (type) {
            case OperationType.insert:
                throw new NodeUpdateError(" ReplaceAroundSteps with 'insert' operation type are not supported ");
            case OperationType.delete:
                // Delete when we are removing the tags around a node.
                return this.replaceAroundDelete(step, mapping.getMapping());
            case OperationType.replace:
                // Replace when we are adding tags around a node
                return this.replaceAroundReplace(step, mapping.getMapping());
        }
    }

    // ReplaceInsert is used when we insert new nodes into the document
    // Note: that these steps can be quite complex, as they can contain multiple (nested) nodes
    //       for example undoing a node deletion 'reinserts' the deleted node(s)
    replaceInsert(step: ReplaceStep, tree: Tree): ParsedStep {
        // We start by checking that there is something to insert in the step
        if (!step.slice.content.childCount) {
            throw new NodeUpdateError(" ReplaceStep insert has no content ");
        }

        // We find the node in the tree that is at the position where we are inserting
        const nodeInTree = tree.findNodeByProsePos(step.from);
        if (!nodeInTree) throw new NodeUpdateError(" Could not find position to insert node in mapping ");
        const parent = tree.findParent(nodeInTree);
        if (!parent) throw new NodeUpdateError(" Could not find parent of insertion position in mapping ");

        // range.to since we are inserting below the node at step.from
        const documentPos = nodeInTree.range.to;

        // let offsetOriginal = nodeInTree.range.to;
        let offsetProse = nodeInTree.pmRange.to;
        let offsetOriginal = nodeInTree.range.to;
        
        const nodes: TreeNode[] = [];
        let serialized = "";
        step.slice.content.forEach(node => {
            const output = this.serializer.serializeNode(node);
            // console.log("OUTPUT", output);
            console.log("node", node.type.name);
            console.log("output", output);
            serialized += output;
            const builtNode = this.buildTreeFromNode(node, offsetOriginal, offsetProse);
            nodes.push(builtNode);
            offsetOriginal += output.length;
            offsetProse += node.nodeSize + (builtNode.innerRange.to - builtNode.innerRange.from);
        });
        
        const docChange: DocChange = {
            startInFile: documentPos,
            endInFile: documentPos,
            finalText: serialized
        };

        const proseOffset = step.slice.content.size;
        const textOffset = serialized.length;

        // now we need to update the tree
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            // Update all nodes that come fully after the insertion position
            if (thisNode.pmRange.from >= nodeInTree.pmRange.to) {
                thisNode.shiftOffsets(textOffset, proseOffset);
            }

            // The inserted nodes could be children of nodes already in the tree (at least of the root node,
            // but possibly also of hint or input nodes)
            if (thisNode.pmRange.from <= nodeInTree.pmRange.from && thisNode.pmRange.to >= nodeInTree.pmRange.to) {
                thisNode.shiftCloseOffsets(textOffset, proseOffset);
            }
        });

        // Add the nodes to the parent node. We do this later so that updating in the step 
        // before does not affect the positions of the nodes we are adding
        nodes.forEach(n => parent.addChild(n));
        
        return { result: docChange, newTree: tree };
    }

    // replaceInsert(step: ReplaceStep, tree: Tree): ParsedStep {
    //     const firstNode = step.slice.content.firstChild;
    //     if (!firstNode) throw new NodeUpdateError(" No nodes in slice content ");

    //     // TODO: The plus 1 does not work when the insert is at the end of some block
    //     console.log("BLABLABLA", tree.findHighestContainingNode(step.from));
    //     const nodeInTree = tree.findNodeByProsemirrorPosition(step.from + 1);
    //     console.log("nodeInTree", JSON.stringify(nodeInTree));
    //     if (!nodeInTree) throw new NodeUpdateError(" Could not find position to insert node in mapping ");
    //     const parent = tree.findParent(nodeInTree);
    //     if (!parent) throw new NodeUpdateError(" Could not find parent of insertion position in mapping ");

        
    //     // let offsetOriginal = nodeInTree.range.to;
    //     let offsetProse = nodeInTree.prosemirrorEnd;
    //     let offsetOriginal = step.from;
    //     console.log("OffsetProse", offsetProse, "OffsetOriginal", offsetOriginal, "Step.from", step.from, "Step.to", step.to);
    //     const nodes: TreeNode[] = [];
    //     let serialized = "";
    //     step.slice.content.forEach(node => {
    //         const output = this.serializer.serializeNode(node);
    //         // console.log("OUTPUT", output);
    //         console.log("node", node.type.name);
    //         console.log("output", output);
    //         serialized += output;
    //         const builtNode = this.buildTreeFromNode(node, offsetOriginal, offsetProse);
    //         nodes.push(builtNode);
    //         offsetOriginal += output.length;
    //         offsetProse += node.nodeSize + (builtNode.innerRange.to - builtNode.innerRange.from);
    //     });
    //     console.log("SERIALIZED BY TEXT SERIALIZE\n", serialized);
    //     console.log("NODES BY BUILD TREE\n", nodes);
        
    //     const docChange: DocChange = {
    //         startInFile: nodeInTree.range.to,
    //         endInFile: nodeInTree.range.to,
    //         finalText: serialized
    //     };

    //     const proseOffset = step.slice.content.size;
    //     const textOffset = serialized.length;

    //     // now we need to update the tree
    //     tree.traverseDepthFirst((thisNode: TreeNode) => {
    //         if (thisNode.prosemirrorStart >= nodeInTree.prosemirrorEnd) {
    //             thisNode.shiftOffsets(textOffset, proseOffset);
    //         }
    //     });

    //     // We add the nodes later so that updating in the step before does not affect the positions of the nodes we are adding
    //     nodes.forEach(n => parent.addChild(n));
        
    //     tree.root.shiftCloseOffsets(textOffset, proseOffset);

    //     return { result: docChange, newTree: tree };
    // }

    

    buildTreeFromNode(node: PNode, startOrig: number, startProse: number): TreeNode {

        // Shortcut for newline nodes
        if (node.type == WaterproofSchema.nodes.newline) {
            return new TreeNode(
                "newline",
                {from: startOrig, to: startOrig + 1},
                {from: startOrig, to: startOrig + 1},
                "",
                startProse, startProse,
                {from: startProse, to: startProse + node.nodeSize}
            );
        }

        const [openTagForNode, closeTagForNode] = this.nodeNameToTagPair(node.type.name, node.attrs.title ? node.attrs.title : "");

        const treeNode = new TreeNode(
            node.type.name, // node type
            {from: startOrig + openTagForNode.length, to: 0}, // inner range
            {from: startOrig, to: 0}, // full range
            node.attrs.title ? node.attrs.title : "", // title
            startProse, 0, // prosemirror start, end
            {from: startProse, to: 0}
        );


        let childOffsetOriginal = startOrig + openTagForNode.length;
        let childOffsetProse = startProse + 1; // +1 for the opening tag

        node.forEach(child => {
            const childTreeNode = this.buildTreeFromNode(child, childOffsetOriginal, childOffsetProse);
            treeNode.children.push(childTreeNode);
            
            // Update the offsets for the next child
            const serializedChild = this.serializer.serializeNode(child);
            childOffsetOriginal += serializedChild.length;
            childOffsetProse += child.nodeSize;
        });

        // Now fill in the to positions for innerRange and range
        treeNode.innerRange.to = childOffsetOriginal;
        treeNode.range.to = childOffsetOriginal + closeTagForNode.length;
        treeNode.prosemirrorEnd = childOffsetProse - 1;
        treeNode.pmRange.to = childOffsetProse;
        return treeNode;
    }

    /**
     * Handles ReplaceSteps that delete content.
     * @param step The ReplaceStep for which we determined that it is deletion of one or more nodes.
     * @param tree The input tree
     * @returns A ParsedStep containing the resulting DocChange and the updated tree.
     */
    replaceDelete(step: ReplaceStep, tree: Tree): ParsedStep {       
        // Find all nodes that are fully in the deleted range
        const nodesToDelete: TreeNode[] = [];
        let from = Number.POSITIVE_INFINITY;
        let to = Number.NEGATIVE_INFINITY;
        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= step.from && node.prosemirrorEnd <= step.to) {
                nodesToDelete.push(node);

                if (node.range.from < from) from = node.range.from;
                if (node.range.to > to) to = node.range.to;

                // Remove from the tree immediately (saves an O(n) traversal over nodesToDelete later)
                const parent = tree.findParent(node);
                if (parent) {
                    parent.removeChild(node);
                }
            }
        });

        console.log("NODES TO DELETE", nodesToDelete);

        if (nodesToDelete.length == 0) {
            throw new NodeUpdateError("Could not find any nodes to delete in the given step.");
        }

        // Create the docChange, the range to remove is from the start of the first node to the end of the last node
        const docChange: DocChange = {
            startInFile: from,
            endInFile: to,
            finalText: ""
        };
        
        // The length of text removed from the original document
        const originalRemovedLength = docChange.endInFile - docChange.startInFile;
        // The total length (as prosemirror indexing) of the nodes removed
        const proseRemovedLength = step.to - step.from;
        
        // Update positions of nodes after the deleted nodes
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            // only shift nodes that come after the deleted nodes
            if (thisNode.prosemirrorStart >= step.to) {
                thisNode.shiftOffsets(-originalRemovedLength, -proseRemovedLength);
            }
        });
        tree.root.shiftCloseOffsets(-originalRemovedLength, -proseRemovedLength);

        return { result: docChange, newTree: tree };
    }

    // ReplaceAroundDelete is used when we unwrap nodes (remove the hint or input tags)
    replaceAroundDelete(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        const firstNodeBeingUnwrapped = tree.findNodeByProsePos(step.gapFrom);
        const lastNodeBeingUnwrapped = tree.findNodeByProsePos(step.gapTo);
        if (!firstNodeBeingUnwrapped || !lastNodeBeingUnwrapped) {
            throw new NodeUpdateError(" Could not find first or last node to unwrap in mapping ");
        }

        // Get all nodes in the range (these are the nodes that will be unwrapped)
        const nodesInRange = tree.nodesInProseRange(firstNodeBeingUnwrapped.pmRange.from, lastNodeBeingUnwrapped.pmRange.to);

        // The wrapperNode should be the parent of the nodes being unwrapped 
        const wrapperNode = tree.findParent(firstNodeBeingUnwrapped);
        if (!wrapperNode) throw new NodeUpdateError(" Could not find parent of nodes being unwrapped ");

        const [wrappedOpenTag, wrappedCloseTag] = this.nodeNameToTagPair(wrapperNode.type, wrapperNode.title);

        // We remove the wrapper node from the tree
        const wrapperParent = tree.findParent(wrapperNode);
        if (!wrapperParent) throw new NodeUpdateError(" Could not find parent of wrapper node ");
        wrapperParent.removeChild(wrapperNode);

        // Create document change
        const docChange: WrappingDocChange = {
            firstEdit: {
                startInFile: wrapperNode.range.from,
                endInFile: wrapperNode.innerRange.from,
                finalText: ""
            },
            secondEdit: {
                startInFile: wrapperNode.innerRange.to,
                endInFile: wrapperNode.range.to,
                finalText: ""
            }
        };

        // First we update all nodes that come totally after the unwrapped node
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            if (thisNode.pmRange.from >= wrapperNode.pmRange.to) {
                // The text positions shift by the length of the open and close tags that have just been removed
                const textOffset = -wrappedOpenTag.length - wrappedCloseTag.length;
                // The prosemirror positions shift by 2 (1 for the opening and 1 for the closing tag)
                const proseOffset = -2;
                thisNode.shiftOffsets(textOffset, proseOffset);
            }
        });

        // Update the root node separately
        tree.root.shiftCloseOffsets(-wrappedOpenTag.length - wrappedCloseTag.length, -2);

        // Now we need to update the nodes that were children of the wrapper node
        nodesInRange.forEach(n => {
            // We update their positions
            n.shiftOffsets(-wrappedOpenTag.length, -1);
            // and add them to the parent of the wrapper node
            wrapperParent.addChild(n);
        });
        
        return { result: docChange, newTree: tree };
    }
    
    replaceAroundReplace(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        console.log("IN REPLACE AROUND REPLACE", step, tree);
        
        // We start by checking what kind of node we are wrapping with
        const wrappingNode = step.slice.content.firstChild;
        if (!wrappingNode) {
            throw new NodeUpdateError(" ReplaceAroundStep replace has no wrapping node ");
        }

        const pmSize = step.slice.size;
        if (pmSize != 2) throw new NodeUpdateError(" Size of the slice is not equal to 2 ");
        
        if (step.slice.content.childCount != 1) {
            throw new NodeUpdateError(" We only support ReplaceAroundSteps with a single wrapping node ");
        }

        // Check that the wrapping node is of a supported type (hint or input)
        const insertedNodeType = wrappingNode.type.name;
        if (insertedNodeType !== "hint" && insertedNodeType !== "input") {
            throw new NodeUpdateError(" We only support wrapping in hints or inputs ");
        }

        // If we are wrapping in a hint node we need to have a title attribute
        const title: string = insertedNodeType === "hint" ? wrappingNode.attrs.title : "";
        // Get the tags for the wrapping node
        const [openTag, closeTag] = this.nodeNameToTagPair(insertedNodeType, title);

        // The step includes a range of nodes that are wrapped. We use the mapping
        // to find the node at gapFrom (the first one being wrapped) and the node
        // at gapTo (the last one being wrapped).
        const nodesBeingWrappedStart = tree.findNodeByProsePos(step.gapFrom);
        const nodesBeingWrappedEnd = tree.findNodeByProsePos(step.gapTo);
        // If one of the two doesn't exist we error
        if (!nodesBeingWrappedStart || !nodesBeingWrappedEnd) throw new NodeUpdateError(" Could not find node in mapping ");

        // Generate the document change (this is a wrapping document change)
        const docChange: WrappingDocChange = {
            firstEdit: {
                finalText: openTag,
                startInFile: nodesBeingWrappedStart.range.from,
                endInFile: nodesBeingWrappedStart.range.from,
            }, 
            secondEdit: {
                finalText: closeTag,
                startInFile: nodesBeingWrappedEnd.range.to,
                endInFile: nodesBeingWrappedEnd.range.to
            }
        };

        // We now update the tree

        const positions = {
            startFrom: nodesBeingWrappedStart.range.from, 
            startTo: nodesBeingWrappedStart.range.to,
            endFrom: nodesBeingWrappedEnd.range.from,
            endTo: nodesBeingWrappedEnd.range.to,
            proseStart: nodesBeingWrappedStart.pmRange.from,
            proseEnd: nodesBeingWrappedEnd.pmRange.to
        };
        
        // Create the new wrapping node
        const newNode = new TreeNode(
            insertedNodeType,
            {from: positions.startFrom + openTag.length, to: positions.endTo}, // inner range
            {from: positions.startFrom, to: positions.endTo + closeTag.length}, // full range
            title,
            positions.proseStart + 1, positions.proseEnd + 1, // prosemirror start, end
            {from: positions.proseStart, to: positions.proseEnd + 2} // pmRange
        );

        // We need to find the parent of the first node being wrapped
        const parent = tree.findParent(nodesBeingWrappedStart);
        if (!parent) throw new NodeUpdateError(" Could not find parent of nodes being wrapped ");

        const nodesInRange = tree.nodesInProseRange(positions.proseStart, positions.proseEnd);
        console.log("NODES IN RANGE", nodesInRange);

        // Remove the nodes that are now children of the new wrapping node from their current parent
        nodesInRange.forEach(n => {
            parent.removeChild(n);
        });
        
        // Finally we need to update all nodes that come after the inserted wrapping node
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            if (thisNode.pmRange.from >= positions.proseEnd) {
                thisNode.shiftOffsets(openTag.length + closeTag.length, 2);
            }
        });

        // Now we need to insert the new wrapping node in the right place in the tree
        parent.addChild(newNode);
        
        nodesInRange.forEach(n => {
            newNode.addChild(n);
            n.shiftOffsets(openTag.length, 1);
        });

        tree.root.shiftCloseOffsets(openTag.length + closeTag.length, 2);

        return {result: docChange, newTree: tree};
    }

}
