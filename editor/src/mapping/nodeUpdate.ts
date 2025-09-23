// Disabled because the ts-ignores later can't be made into ts-expect-error
/* eslint-disable @typescript-eslint/ban-ts-comment */
import { ReplaceAroundStep, ReplaceStep, Node as PNode, WaterproofSchema, WrappingDocChange, TagMap } from "@impermeable/waterproof-editor";
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
    constructor (private tagMap: TagMap) {} 


    nodeNameToTagPair(nodeName: string, title: string = ""): [string, string] {
        switch (nodeName) {
            case "markdown":
                return [this.tagMap.markdownOpen, this.tagMap.markdownClose];
            case "code":
                return [this.tagMap.codeOpen, this.tagMap.codeClose];
            case "hint":
                return [this.tagMap.hintOpen(title), this.tagMap.hintClose];
            case "input":
                return [this.tagMap.inputOpen, this.tagMap.inputClose];
            case "math_display":
                return [this.tagMap.mathOpen, this.tagMap.mathClose];
            default:
                throw new Error(`Unsupported node type: ${nodeName}`);
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
                throw new Error(" We do not support ReplaceSteps that replace nodes with other nodes (textual replaces are handled in the textUpdate module) ");
        }
    }

    doReplaceAroundStep(step: ReplaceAroundStep, mapping: TextDocMappingNew): ParsedStep {
        // Determine operation type
        const type = typeFromStep(step);
        switch (type) {
            case OperationType.insert:
                throw new Error(" ReplaceAroundSteps with 'insert' operation type are not yet supported ");
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
        // // TOO General
        // step.slice.content.descendants((node) => {
        //     inBetweenText += serializeNode(node);
        // })

        const firstNode = step.slice.content.firstChild;
        if (!firstNode) throw new Error(" No nodes in slice content ");

        // Get the nodes before and after the insertion point (if any)
        const nodeBefore = tree.findNodeByProsemirrorPosition(step.from - 1);
        const nodeAfter = tree.findNodeByProsemirrorPosition(step.to + 1);
        
        const insertedNodeType = step.slice.content.firstChild.type.name;
        const newlineBefore = (nodeBefore !== null && insertedNodeType == "code");
        const newlineAfter = (nodeAfter !== null && nodeAfter.type !== "code" && insertedNodeType == "code");
        const {open, close, content, title} = this.serializeNode(step.slice.content.firstChild, newlineBefore, newlineAfter);
        
        const docChange: DocChange = {
            startInFile: nodeBefore !== null ? nodeBefore.range.to: 0,
            endInFile: nodeBefore !== null ? nodeBefore.range.to: 0,
            finalText: open + content + close
        }
        
        const nodeToInsert = new TreeNode(
            insertedNodeType, // node type
            // FIXME: Why -1 here?
            { from: docChange.startInFile + open.length - 1, to: docChange.startInFile + open.length + title.length + content.length }, // Document (inner range) positions
            { from: docChange.startInFile, to: docChange.startInFile + open.length + title.length + content.length + close.length }, // Document (full range) positions
            // docChange.startInFile + open.length, docChange.startInFile + open.length + title.length + content.length, // Document (inner range) positions
            title, // Title
            (nodeBefore !== null ? nodeBefore.prosemirrorEnd : 0) + 1, (nodeBefore !== null ? nodeBefore.prosemirrorEnd : 0) + content.length + 2, // Prosemirror positions
            content // String content
        );

        const prosemirrorOffset = 2 + content.length;
        const originalOffset = open.length + close.length + content.length + title.length;
        // now we need to update the tree
        tree.traverseDepthFirst((node: TreeNode) => {
            // Every node after the inserted node needs to be shifted
            if (node.prosemirrorStart >= nodeToInsert.prosemirrorEnd) {
                node.shiftOffsets(originalOffset, prosemirrorOffset);
            }
        });

        tree.insertByPosition(nodeToInsert);

        tree.root.shiftCloseOffsets(originalOffset, prosemirrorOffset);

        return { result: docChange, newTree: tree };
    }

    serializeNode(
        node: PNode,
        includeStartNewline: boolean = false,
        includeEndNewline: boolean = false
    ): { open: string, close: string, content: string, title: string } {
        let open = "";
        let close = "";
        const content = node.textContent;
        let title = "";

        if (node.type == WaterproofSchema.nodes.markdown) {
            open = this.tagMap.markdownOpen;
            close = this.tagMap.markdownClose;
        } else if (node.type == WaterproofSchema.nodes.code) {
            open = this.tagMap.codeOpen;
            close = this.tagMap.codeClose;
        } else if (node.type == WaterproofSchema.nodes.hint) {
            title = node.attrs.title;
            open = this.tagMap.hintOpen(title);
            close = this.tagMap.hintClose;
        } else if (node.type == WaterproofSchema.nodes.input) {
            open = this.tagMap.inputOpen;
            close = this.tagMap.inputClose;
        } else if (node.type == WaterproofSchema.nodes.math_display) {
            open = this.tagMap.mathOpen;
            close = this.tagMap.mathClose;
        } else {
            throw new Error(`Unsupported node type: ${node.type.name}`);
        }

        if (includeStartNewline) open = "\n" + open;
        if (includeEndNewline) close = close + "\n";

        return { open, close, content, title };
    }

    replaceDelete(step: ReplaceStep, tree: Tree): ParsedStep {
        // TODO: Assumes that we are deleting a single node.

        // Find the node to delete at the given Prosemirror position
        const deletedNode = tree.findNodeByProsemirrorPosition(step.from + 1);
        if (!deletedNode) {
            throw new Error("Could not find node to delete at the given position.");
        }


        console.log("Deleting node", deletedNode);


        // Compute the document change: remove the node's text from the file
        const docChange: DocChange = {
            startInFile: deletedNode.range.from,
            endInFile: deletedNode.range.to,
            finalText: ""
        };

        // Remove the node from the tree
        const parent = tree.findParent(deletedNode);
        if (parent) {
            parent.removeChild(deletedNode);
        } 

        // Calculate offsets for updating positions
        const proseOffset = 2 + deletedNode.innerRange.to - deletedNode.innerRange.from;
        const textOffset = deletedNode.range.to - deletedNode.range.from;

        // Update positions of nodes after the deleted node
        tree.traverseDepthFirst((thisNode: TreeNode) => {
            // only shift nodes that come after the deleted node
            if (thisNode.prosemirrorStart > deletedNode.prosemirrorEnd) {
                thisNode.shiftOffsets(-textOffset, -proseOffset);
            }
        });

        // Update the root node's closing position
        tree.root.shiftCloseOffsets(-textOffset, -proseOffset);

        return { result: docChange, newTree: tree };
    }

    replaceAroundDelete(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        console.log("IN REPLACE AROUND DELETE", step, tree);
        
        // TODO: Assuming we are always unwrapping a single node

        const nodeBeingUnwrapped = tree.findNodeByProsemirrorPosition(step.gapFrom + 1);
        if (!nodeBeingUnwrapped) throw new Error(" Could not find the node to be lifted in mapping ");
        console.log("NODE BEING UNWRAPPED", nodeBeingUnwrapped);

        const nodeBeingUnwrapped2 = tree.findNodeByProsemirrorPosition(step.gapTo - 1);
        console.log("NODE BEING UNWRAPPED 2", nodeBeingUnwrapped2);

        const nodeBefore = tree.findNodeByProsemirrorPosition(step.from - 1);
        const nodeAfter = tree.findNodeByProsemirrorPosition(step.to + 1);
        console.log("NODE BEFORE", nodeBefore, "NODE AFTER", nodeAfter);

        const wrapperNode = tree.findNodeByProsemirrorPosition(step.from + 1);
        if (!wrapperNode) throw new Error(" Could not find the wrapper node in mapping ");
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
            throw new Error(" ReplaceAroundStep replace has no wrapping node ");

        if (step.slice.content.childCount != 1) {
            throw new Error(" We only support ReplaceAroundSteps with a single wrapping node ");
        }

        const insertedNodeType = wrappingNode.type.name;
        if (insertedNodeType !== "hint" && insertedNodeType !== "input")
            throw new Error(" We only support wrapping in hints or inputs ");

    
        const title: string = insertedNodeType === "hint" ? wrappingNode.attrs.title : "";
        const [openTag, closeTag] = this.nodeNameToTagPair(insertedNodeType, title);

        // Find the node being wrapped
        const nodeBeingWrapped = tree.findNodeByProsemirrorPosition(step.gapFrom + 1);
        if (!nodeBeingWrapped) throw new Error(" Could not find node in mapping ");
        console.log("NODE", nodeBeingWrapped);

        const originalOuter = {from: nodeBeingWrapped.range.from, to: nodeBeingWrapped.range.to};
        const originalInner = {from: nodeBeingWrapped.innerRange.from, to: nodeBeingWrapped.innerRange.to};
        const originalProsemirror = {from: nodeBeingWrapped.prosemirrorStart, to: nodeBeingWrapped.prosemirrorEnd};
        
        // const [openTagExisting, closeTagExisting] = nodeNameToTagPair(nodeBeingWrapped.type);
        const isCode = nodeBeingWrapped.type === "code";

        // In the case of code blocks we have to be careful to preserve the newlines

        if (isCode) {
            const codeOpen = this.tagMap.codeOpen;
            const codeClose = this.tagMap.codeClose;
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
