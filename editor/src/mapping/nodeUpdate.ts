import { ReplaceAroundStep, ReplaceStep, Node as PNode, WaterproofSchema, WrappingDocChange, NodeUpdateError, TagConfiguration, DocumentSerializer } from "@impermeable/waterproof-editor";
import { Tree, TreeNode } from "./Tree";
import { OperationType, ParsedStep } from "./types";
import { DocChange } from "@impermeable/waterproof-editor";
import { TextDocMappingNew } from "./newmapping";

function typeFromStep(step: ReplaceStep | ReplaceAroundStep): OperationType {
    if (step.from == step.to) return OperationType.insert;
    if (step.slice.content.firstChild == null) {
        return OperationType.delete;
    } else {
        return OperationType.replace;
    }
}

export class NodeUpdate {
    constructor (private tagConf: TagConfiguration, private serializer: DocumentSerializer) {} 


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

    doReplaceStep(step: ReplaceStep, mapping: TextDocMappingNew): ParsedStep {
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

    doReplaceAroundStep(step: ReplaceAroundStep, mapping: TextDocMappingNew): ParsedStep {
        // Determine operation type
        const type = typeFromStep(step);
        switch (type) {
            case OperationType.insert:
                throw new NodeUpdateError(" ReplaceAroundSteps with 'insert' operation type are not yet supported ");
            case OperationType.delete:
                // Delete when we are removing the tags around a node.
                return this.replaceAroundDelete(step, mapping.getMapping());
            case OperationType.replace:
                // Replace when we are adding tags around a node
                return this.replaceAroundReplace(step, mapping.getMapping());
        }
    }

    public nodeUpdate(step: ReplaceStep | ReplaceAroundStep, mapping: TextDocMappingNew) : ParsedStep {
        console.log("IN NODE UPDATE", step, mapping.getMapping());

        let parsedStep;
        if (step instanceof ReplaceStep) {
            parsedStep = this.doReplaceStep(step, mapping);
        } else {
            parsedStep = this.doReplaceAroundStep(step, mapping);
        }

        console.log("TREEEE", JSON.stringify(parsedStep.newTree));
        return parsedStep;
    }

    replaceInsert(step: ReplaceStep, tree: Tree): ParsedStep {
        const firstNode = step.slice.content.firstChild;
        if (!firstNode) throw new NodeUpdateError(" No nodes in slice content ");

        // TODO: The plus 1 does not work when the insert is at the end of some block
        console.log("BLABLABLA", tree.findHighestContainingNode(step.from));
        const nodeInTree = tree.findNodeByProsemirrorPosition(step.from + 1);
        console.log("nodeInTree", JSON.stringify(nodeInTree));
        if (!nodeInTree) throw new NodeUpdateError(" Could not find position to insert node in mapping ");
        const parent = tree.findParent(nodeInTree);
        if (!parent) throw new NodeUpdateError(" Could not find parent of insertion position in mapping ");

        
        // let offsetOriginal = nodeInTree.range.to;
        let offsetProse = nodeInTree.prosemirrorEnd;
        let offsetOriginal = step.from;
        console.log("OffsetProse", offsetProse, "OffsetOriginal", offsetOriginal, "Step.from", step.from, "Step.to", step.to);
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
        console.log("SERIALIZED BY TEXT SERIALIZE\n", serialized);
        console.log("NODES BY BUILD TREE\n", nodes);
        
        
        
        const docChange: DocChange = {
            startInFile: nodeInTree.range.to,
            endInFile: nodeInTree.range.to,
            finalText: serialized
        };

        const proseOffset = step.slice.content.size;
        const textOffset = serialized.length;

        // now we need to update the tree
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            if (thisNode.prosemirrorStart >= nodeInTree.prosemirrorEnd) {
                thisNode.shiftOffsets(textOffset, proseOffset);
            }
        });

        // We add the nodes later so that updating in the step before does not affect the positions of the nodes we are adding
        nodes.forEach(n => parent.addChild(n));
        
        tree.root.shiftCloseOffsets(textOffset, proseOffset);

        return { result: docChange, newTree: tree };
    }

    

    buildTreeFromNode(node: PNode, startOrig: number, startProse: number): TreeNode {

        // Shortcut for newline nodes
        if (node.type == WaterproofSchema.nodes.newline) {
            return new TreeNode(
                "newline",
                {from: startOrig, to: startOrig + 1},
                {from: startOrig, to: startOrig + 1},
                "",
                startProse, startProse + node.nodeSize,
                ""
            );
        }

        const [openTagForNode, closeTagForNode] = this.nodeNameToTagPair(node.type.name, node.attrs.title ? node.attrs.title : "");

        const treeNode = new TreeNode(
            node.type.name, // node type
            {from: startOrig + openTagForNode.length, to: 0}, // inner range
            {from: startOrig, to: 0}, // full range
            node.attrs.title ? node.attrs.title : "", // title
            startProse, 0, // prosemirror start, end
            ""
        );

        const serialized = this.serializer.serializeNode(node);

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
        treeNode.stringContent = serialized.substring(openTagForNode.length, serialized.length - closeTagForNode.length);
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

    replaceAroundDelete(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        console.log("IN REPLACE AROUND DELETE", step, tree);
        
        // TODO: Assuming we are always unwrapping a single node

        const nodeBeingUnwrapped = tree.findNodeByProsemirrorPosition(step.gapFrom + 1);
        if (!nodeBeingUnwrapped) throw new NodeUpdateError(" Could not find the node to be lifted in mapping ");
        console.log("NODE BEING UNWRAPPED", nodeBeingUnwrapped);

        const nodeBeingUnwrapped2 = tree.findNodeByProsemirrorPosition(step.gapTo - 1);
        console.log("NODE BEING UNWRAPPED 2", nodeBeingUnwrapped2);

        const nodeBefore = tree.findNodeByProsemirrorPosition(step.from - 1);
        const nodeAfter = tree.findNodeByProsemirrorPosition(step.to + 1);
        console.log("NODE BEFORE", nodeBefore, "NODE AFTER", nodeAfter);

        const wrapperNode = tree.findNodeByProsemirrorPosition(step.from + 1);
        if (!wrapperNode) throw new NodeUpdateError(" Could not find the wrapper node in mapping ");
        console.log("WRAPPER NODE", wrapperNode);

        const wrapperOuter = {from: wrapperNode.range.from, to: wrapperNode.range.to};
        const wrapperInner = {from: wrapperNode.innerRange.from, to: wrapperNode.innerRange.to};
        const unwrappedOuter = {from: nodeBeingUnwrapped.range.from, to: nodeBeingUnwrapped.range.to};
        const unwrappedInner = {from: nodeBeingUnwrapped.innerRange.from, to: nodeBeingUnwrapped.innerRange.to};
        

        const [wrappedOpenTag, wrappedCloseTag] = this.nodeNameToTagPair(wrapperNode.type, wrapperNode.title);
        // const startsWithNewline = wrapperInner.from > wrappedOuter.from + wrappedOpenTag.length;
        // const endsWithNewline = wrappedOuter.to > wrappedInner.to + wrappedCloseTag.length;

        const docChange: WrappingDocChange = {
            firstEdit: {
                startInFile: wrapperOuter.from,
                endInFile: wrapperInner.from,
                finalText: ""
            },
            secondEdit: {
                startInFile: wrapperInner.to,
                endInFile: wrapperOuter.to,
                finalText: ""
            }
        };

        // Create a copy of the node being unwrapped with updated ranges
        const copyNodeBeingUnwrapped = new TreeNode(
            nodeBeingUnwrapped.type,
            // inner
            { from: wrapperOuter.from + (unwrappedInner.from - unwrappedOuter.from), to: nodeBeingUnwrapped.innerRange.to - wrappedOpenTag.length },
            // outer
            { from: wrapperOuter.from, to: wrapperOuter.from + wrapperInner.to - wrapperInner.from },
            nodeBeingUnwrapped.title,
            nodeBeingUnwrapped.prosemirrorStart - 1, nodeBeingUnwrapped.prosemirrorEnd - 1,
            nodeBeingUnwrapped.stringContent
        );
        // Update the tree
        // Remove the node that is being unwrapped.
        tree.root.removeChild(wrapperNode);
        // Update the tree positions.
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            // Update everything after the unwrapped node
            if (thisNode.range.from >= wrapperOuter.to) {
                thisNode.shiftOffsets(-wrappedOpenTag.length - wrappedCloseTag.length, -2);
            }
        });
        tree.root.shiftCloseOffsets(-wrappedOpenTag.length - wrappedCloseTag.length, -2);

        tree.root.addChild(copyNodeBeingUnwrapped);

        return { result: docChange, newTree: tree };
    }

    replaceAroundReplace(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        console.log("IN REPLACE AROUND REPLACE", step, tree);

        // Get the nodes before and after the node that we are wrapping.
        const nodeBefore = tree.findNodeByProsemirrorPosition(step.from - 1);
        const nodeAfter = tree.findNodeByProsemirrorPosition(step.to + 1);
        const hasCodeBefore = nodeBefore !== null && nodeBefore.type === "code";
        const hasCodeAfter = nodeAfter !== null && nodeAfter.type === "code";

        const wrappingNode = step.slice.content.firstChild;
        if (!wrappingNode)
            throw new NodeUpdateError(" ReplaceAroundStep replace has no wrapping node ");

        if (step.slice.content.childCount != 1) {
            throw new NodeUpdateError(" We only support ReplaceAroundSteps with a single wrapping node ");
        }

        const insertedNodeType = wrappingNode.type.name;
        if (insertedNodeType !== "hint" && insertedNodeType !== "input")
            throw new NodeUpdateError(" We only support wrapping in hints or inputs ");

    
        const title: string = insertedNodeType === "hint" ? wrappingNode.attrs.title : "";
        const [openTag, closeTag] = this.nodeNameToTagPair(insertedNodeType, title);

        // Find the node being wrapped
        const nodeBeingWrapped = tree.findNodeByProsemirrorPosition(step.gapFrom + 1);
        if (!nodeBeingWrapped) throw new NodeUpdateError(" Could not find node in mapping ");
        console.log("NODE", nodeBeingWrapped);

        const originalOuter = {from: nodeBeingWrapped.range.from, to: nodeBeingWrapped.range.to};
        const originalInner = {from: nodeBeingWrapped.innerRange.from, to: nodeBeingWrapped.innerRange.to};
        const originalProsemirror = {from: nodeBeingWrapped.prosemirrorStart, to: nodeBeingWrapped.prosemirrorEnd};
        
        // const [openTagExisting, closeTagExisting] = nodeNameToTagPair(nodeBeingWrapped.type);
        const isCode = nodeBeingWrapped.type === "code";

        // In the case of code blocks we have to be careful to preserve the newlines

        if (isCode) {
            const codeOpen = this.tagConf.code.openTag;
            const codeClose = this.tagConf.code.closeTag;
            const startsWithNewline = originalInner.from > originalOuter.from + codeOpen.length;
            const endsWithNewline = originalOuter.to > originalInner.to + codeClose.length;

            const docChange: WrappingDocChange = {
                firstEdit: {
                    startInFile: nodeBeingWrapped.range.from,
                    endInFile: nodeBeingWrapped.range.from,
                    finalText: (hasCodeBefore ? "\n" : "") + openTag + (startsWithNewline ? "" : "\n")
                },
                secondEdit: {
                    startInFile: nodeBeingWrapped.range.to,
                    endInFile: nodeBeingWrapped.range.to,
                    finalText:  (endsWithNewline ? "" : "\n") + closeTag + (hasCodeAfter ? "\n" : "")
                }
            };

            // Create a copy of the node being wrapped with updated ranges
            const copyNodeBeingWrapped = new TreeNode(
                nodeBeingWrapped.type,
                { from: originalInner.from + openTag.length + (startsWithNewline ? 0 : 1), to: originalInner.to + openTag.length + (startsWithNewline ? 0 : 1) },
                { from: originalOuter.from + openTag.length - (startsWithNewline ? 0 : 1), to: originalOuter.to + openTag.length - (startsWithNewline ? 0 : 1) + (endsWithNewline ? 0 : 1) },
                nodeBeingWrapped.title,
                originalProsemirror.from + 1 - (startsWithNewline ? 0 : 1), originalProsemirror.to + 1,
                nodeBeingWrapped.stringContent
            );
            // copyNodeBeingWrapped.shiftOffsets((hasCodeBefore ? 1 : 0), 0);
            // Update the tree
            const wrappingNode = new TreeNode(
                insertedNodeType, // node type
                { from: originalOuter.from + openTag.length, to: originalOuter.to + openTag.length + (endsWithNewline ? 0 : 1) + (startsWithNewline ? 0 : 1)}, // Document (inner range) positions
                { from: originalOuter.from, to: originalOuter.to + openTag.length + closeTag.length + (startsWithNewline ? 0 : 1) + (endsWithNewline ? 0 : 1) }, // Document (full range) positions
                title, // Title
                originalProsemirror.from, originalProsemirror.to + 2, // Prosemirror positions
                "" // String content
            );
            // If we have added a newline before the tag then we should shift this node
            wrappingNode.shiftOffsets((hasCodeBefore ? 1 : 0), 0);

            // The surrounding code cells absorb the newline(s) that is(/are) added.
            if (hasCodeAfter) nodeAfter.range.from -= 1;
            if (hasCodeBefore) nodeBefore.range.to += 1;
            
            // The wrapping node contains the updated copy of the node being wrapped
            wrappingNode.children = [copyNodeBeingWrapped];
            // Remove the node that is being wrapped.
            tree.root.removeChild(nodeBeingWrapped);
            // Update the tree positions.
            tree.traverseDepthFirst((thisNode: TreeNode) => {
                // Update everything after the inserted node
                if (thisNode.range.from > originalOuter.to) {
                    thisNode.shiftOffsets(openTag.length + closeTag.length + (startsWithNewline ? 0 : 1) + (endsWithNewline ? 0 : 1), 2);
                    thisNode.shiftOffsets((hasCodeBefore ? 1 : 0) + (hasCodeAfter ? 1 : 0));
                }
            });

            tree.root.shiftCloseOffsets(openTag.length + closeTag.length + (startsWithNewline ? 0 : 1) + (endsWithNewline ? 0 : 1), 2);

            tree.root.addChild(wrappingNode);

            return { result: docChange, newTree: tree };
        } else {
            const docChange: WrappingDocChange = {
                firstEdit: {
                    startInFile: nodeBeingWrapped.range.from,
                    endInFile: nodeBeingWrapped.range.from,
                    finalText: openTag
                }, 
                secondEdit: {
                    startInFile: nodeBeingWrapped.range.to,
                    endInFile: nodeBeingWrapped.range.to,
                    finalText: closeTag 
                }
            }

            // Create a copy of the node being wrapped with updated ranges
            const copyNodeBeingWrapped = new TreeNode(
                nodeBeingWrapped.type,
                { from: originalInner.from + openTag.length, to: originalInner.to + openTag.length },
                { from: originalOuter.from + openTag.length, to: originalOuter.to + openTag.length },
                nodeBeingWrapped.title,
                originalProsemirror.from + 1, originalProsemirror.to + 1,
                nodeBeingWrapped.stringContent
            );

            // Update the tree
            const wrappingNode = new TreeNode(
                insertedNodeType, // node type
                { from: originalOuter.from + openTag.length, to: originalOuter.to + openTag.length }, // Document (inner range) positions
                { from: originalOuter.from, to: originalOuter.to + openTag.length + closeTag.length }, // Document (full range) positions
                title, // Title
                originalProsemirror.from, originalProsemirror.to + 2, // Prosemirror positions
                "" // String content
            );
            // The wrapping node contains the updated copy of the node being wrapped
            wrappingNode.children = [copyNodeBeingWrapped];
            
            // Remove the node that is being wrapped.
            tree.root.removeChild(nodeBeingWrapped);
            
            // Update the tree positions.
            tree.traverseDepthFirst((thisNode: TreeNode) => {
                // Update everything after the inserted node
                if (thisNode.range.from > originalOuter.from) {
                    thisNode.shiftOffsets(openTag.length + closeTag.length, 2);
                }
            });

            tree.root.shiftCloseOffsets(openTag.length + closeTag.length, 2);
            // TODO: This assumes we are always wrapping at the root level.
            tree.root.addChild(wrappingNode);

            return { result: docChange, newTree: tree };
        }
    }

}
