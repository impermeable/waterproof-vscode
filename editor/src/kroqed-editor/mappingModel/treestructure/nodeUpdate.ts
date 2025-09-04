// Disabled because the ts-ignores later can't be made into ts-expect-error
/* eslint-disable @typescript-eslint/ban-ts-comment */
import { ReplaceAroundStep, ReplaceStep } from "prosemirror-transform";
import { Tree, TreeNode } from "./Tree";
import { DocChange, WrappingDocChange } from "../../../../../shared";
import { OperationType, ParsedStep } from "./types";
import { getEndHtmlTagText, getStartHtmlTagText, getTextOffset, parseFragment } from "../mvFile/helper-functions";


// TO BE IMPLEMENTED!
export class NodeUpdate {

    /** Used to parse a step that causes nodes to be updated instead of just text */
    static nodeUpdate(step: ReplaceStep | ReplaceAroundStep, tree: Tree) : ParsedStep {
        let result : ParsedStep;

        /** Get the doc change and do some error checking */
        if (step instanceof ReplaceStep) {
            // Determine operation type
            let type: OperationType = OperationType.delete;
            if (step.from == step.to) type = OperationType.insert;

            // We only support pure insertions and deletions
            //if (type == OperationType.delete && step.slice.content.firstChild !== null) throw new Error(" We support ReplaceStep for nodes, but, only, as pure insertions and deletions ");

            // Check that the slice conforms to our assumptions
            if (step.slice.openStart != 0 || step.slice.openEnd != 0) throw new Error(" We do not support partial slices for ReplaceSteps");

            if (type === OperationType.delete) {
                // Is the node deletion in a valid location

                if (tree.findNodeByProsemirrorPosition(step.from) == null || tree.findNodeByProsemirrorPosition(step.to) == null) {
                    throw new Error(" Mapping does not contain this position, is node inserted in middle of another node?");
                }
                result = NodeUpdate.replaceStepDelete(step,tree);
            } else {
                result = NodeUpdate.replaceStepInsert(step,tree);
            }
        } else {
            // Replace around step in valid form
            if (step.gapFrom - step.from > 1 || step.to - step.gapTo > 1) throw new Error(" We only support ReplaceAroundSteps with a single gap");

            // Deletion ReplaceAroundstep
            if (step.slice.content.firstChild == null) {
                // Error check Deletion step
                if (tree.findNodeByProsemirrorPosition(step.from) == null || tree.findNodeByProsemirrorPosition(step.gapFrom) == null) {
                    throw new Error(" ReplaceAroundStep deletion is in unconventional form");
                }
                if (tree.findNodeByProsemirrorPosition(step.gapTo) == null || tree.findNodeByProsemirrorPosition(step.to) == null) {
                    throw new Error(" ReplaceAroundStep deletion is in unconventional form");
                }

                result = NodeUpdate.replaceAroundStepDelete(step,tree);
            } else if (step.slice.content.childCount == 1 && step.slice.openStart == 0 && step.slice.openEnd == 0) {
                // Error check ReplaceAroundStep insertion
                if (step.gapFrom - step.from > 0 || step.to - step.gapTo > 0 || step.insert != 1) throw new Error(" We only support ReplaceAroundStep that inserts chunk in single node");
                if (tree.findNodeByProsemirrorPosition(step.from) == null || tree.findNodeByProsemirrorPosition(step.to) == null) {
                    throw new Error(" Not a proper wrapping ");
                }
                if(!(step.slice.content.firstChild.type.name == 'hint' || step.slice.content.firstChild.type.name == 'input')) throw new Error(" We only support wrapping in hints or inputs ");

                result = NodeUpdate.replaceAroundStepInsert(step,tree);
            } else {
                throw new Error(" We do not support this type of ReplaceAroundStep");
            }
        }
        return result;        
    }

    private static replaceStepDelete(step: ReplaceStep, tree: Tree) : ParsedStep {
        //// Determine the in text document change vscode side

        /** The resulting change of this step operation */
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }

        /** Determine the resulting DocChange indices */
        const deletedNode = tree.findNodeByProsemirrorPosition(step.from);
        if (!deletedNode) throw new Error("We could not find the correct node");
        result.startInFile = deletedNode.originalStart;
        result.endInFile = deletedNode.originalEnd;

        //// Update the mapping to reflect the new prosemirror state

        // The offsets that were deleted from the doc needed to update the mappings
        const proseStart = deletedNode?.prosemirrorStart ?? 0;
        const proseEnd = deletedNode?.prosemirrorEnd ?? 0;
        const proseOffset = proseStart - proseEnd;
        const textStart = deletedNode?.originalStart ?? 0;
        const textEnd = deletedNode?.originalEnd ?? 0;
        const textOffset = textStart- textEnd;
        // Update positions in the tree
        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= proseStart && node.prosemirrorEnd <= proseEnd) {
                // Remove the node from the tree
                const parent = tree.findParent(deletedNode);
                if (parent) {
                    parent.removeChild(deletedNode);
                } else {
                    // maybe it's the root
                    if (tree.root === deletedNode) {
                        tree.root = null; 
                    }
                }
            }
            if (node.prosemirrorStart > proseStart) {
                node.prosemirrorStart += proseOffset;
                node.prosemirrorEnd += proseOffset;
            }
            if (node.originalStart > textStart) {
                node.originalStart += textOffset;
                node.originalEnd += textOffset;
            }
        });
        let newTree = new Tree;
        newTree = tree;
        return {result, newTree};
    }

    /** Converts a replace step that is a pure node update to a DocChange */
    private static replaceStepInsert(step: ReplaceStep, tree: Tree) : ParsedStep {
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }
        let final;
        let inBetweenText: string = "";

        if (tree.root?.children.length == 0) {
            final = parseFragment(step.slice.content);
            if (step.slice.content.firstChild!.content.firstChild !== null) inBetweenText = step.slice.content.firstChild!.content.firstChild.textContent;

            /** Compute the resulting DocChange */
            result.startInFile = 0;
            result.endInFile = 0;
            result.finalText = final.starttext + inBetweenText + final.endtext;
        } else {
            const node = tree.findNodeByProsemirrorPosition(step.from);
            if (!node) throw new Error("We could not find the correct node");
            final = parseFragment(step.slice.content);

            /** Compute the resulting DocChange */
            //TODO: check if this is correct
            result.startInFile = node.originalStart + final.starttext.length;
            result.endInFile = result.startInFile;
            result.finalText = final.starttext + final.endtext;

            const proseStart = node.prosemirrorStart + final.proseOffset;
            const proseEnd = proseStart + step.slice.content.size + final.proseOffset;
            const proseOffset = proseStart - proseEnd;
            const textStart = node.originalStart + final.starttext.length;
            const textEnd = node.originalEnd + final.endtext.length;
            const textOffset = textStart - textEnd;
            ///Update existing mapping
            tree.traverseDepthFirst((node: TreeNode) => {
                if (node.prosemirrorStart > proseStart) {
                    node.prosemirrorStart += proseOffset;
                    node.prosemirrorEnd += proseOffset;
                }
                if (node.originalStart > textStart) {
                    node.originalStart += textOffset;
                    node.originalEnd += textOffset;
                }
            });
            
            let fragmentNode = step.slice.content.firstChild;
            let childNodes: TreeNode[] = [];
            childNodes.push(node)
            let index = 1;
            while (fragmentNode) {
                // Create a new TreeNode for the child
                let childNode = new TreeNode(
                    fragmentNode.type.name,
                    node.originalStart + final.starttext.length,
                    fragmentNode.textContent.length,
                    node.prosemirrorStart + final.proseOffset,
                    node.prosemirrorEnd + final.proseOffset,
                    fragmentNode.textContent || ""
                );
                childNodes.push(childNode);

                childNodes[index - 1].addChild(childNode);

                index++;

                fragmentNode = fragmentNode.content.firstChild;
            }

        }
        let newTree = new Tree;
        newTree = tree;
        return {result, newTree};

    }

    /** Setups the wrapping doc change for the suceeding functions */
    private static setupWrapper() : WrappingDocChange {
        const edit1: DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }; 
        const edit2: DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        };

        /** The resulting document change to document model */
        const result: WrappingDocChange = {
            firstEdit: edit1,
            secondEdit: edit2
        }; 
        return result;
    }

    private static replaceAroundStepDelete(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        const result: WrappingDocChange = {
            firstEdit:  { startInFile: 0, endInFile: 0, finalText: "" },
            secondEdit: { startInFile: 0, endInFile: 0, finalText: "" },
        };

        const wrapper = tree.findNodeByProsemirrorPosition(step.from);
        if (!wrapper) throw new Error("Wrapper node not found at step.from");
        if (wrapper.prosemirrorStart !== step.from || wrapper.prosemirrorEnd !== step.to) {
            throw new Error("ReplaceAroundStep delete must unwrap a whole node");
        }

        const startTag = getStartHtmlTagText(wrapper.type);
        const endTag   = getEndHtmlTagText(wrapper.type);

        result.firstEdit.startInFile = wrapper.originalStart - startTag.length;
        result.firstEdit.endInFile   = wrapper.originalStart;
        result.firstEdit.finalText   = "";

        result.secondEdit.startInFile = wrapper.originalEnd;
        result.secondEdit.endInFile   = wrapper.originalEnd + endTag.length;
        result.secondEdit.finalText   = "";

        let parent: TreeNode | null = null;
        let insertIndex = -1;

        tree.traverseDepthFirst((node: TreeNode) => {
            if (parent) return;                 
            const idx = node.children.indexOf(wrapper);
            if (idx !== -1) {
                parent = node;
                insertIndex = idx;
            }
        });

        if (!parent) throw new Error("Cannot unwrap the root node");

        const liftedChildren = [...wrapper.children];
        (parent as TreeNode).children.splice(insertIndex, 1, ...liftedChildren);

        const cut1 = wrapper.originalStart;
        const cut2 = wrapper.originalEnd;
        const startLen = getStartHtmlTagText(wrapper.type).length;
        const endLen   = getEndHtmlTagText(wrapper.type).length;

        tree.traverseDepthFirst(node => {
            if (node.originalStart >= cut2) {
                node.originalStart -= (startLen + endLen);
                node.originalEnd   -= (startLen + endLen);
            } else if (node.originalStart >= cut1) {
                node.originalStart -= startLen;
                node.originalEnd   -= startLen;
            }
        });

        const cutPM1 = step.gapFrom;
        const cutPM2 = step.to;

        tree.traverseDepthFirst(node => {
            if (node.prosemirrorStart >= cutPM2) {
                node.prosemirrorStart -= 2;
                node.prosemirrorEnd   -= 2;
            } else if (node.prosemirrorStart >= cutPM1) {
                node.prosemirrorStart -= 1;
                node.prosemirrorEnd   -= 1;
            }
        });

        return { result, newTree: tree };
    }



    private static replaceAroundStepInsert(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        const result: WrappingDocChange = {
            firstEdit:  { startInFile: 0, endInFile: 0, finalText: "" },
            secondEdit: { startInFile: 0, endInFile: 0, finalText: "" },
        };

        const wrapType = step.slice.content.firstChild?.type.name;
        if (!(wrapType === "hint" || wrapType === "input")) {
            throw new Error("We only support wrapping in hints or inputs");
        }

        let parent: TreeNode | null = null;
        let startIdx = -1;
        let endIdx = -1;

        tree.traverseDepthFirst((n: TreeNode) => {
            if (parent) return; 
            if (!n.children.length) return;
            for (let i = 0; i < n.children.length; i++) {
                if (n.children[i].prosemirrorStart === step.from && n.children[i].prosemirrorEnd   === step.to) {
                    parent = n;
                    break;
                }
            }
        });

        if (!parent || startIdx === -1 || endIdx === -1 || endIdx < startIdx) {
            throw new Error("ReplaceAroundStep insert must wrap a contiguous sibling range");
        }

        if (!parent) {
            throw new Error("Cannot wrap the root node");
        }
        const firstChild = parent.children[startIdx];
        const lastChild  = parent.children[endIdx];

        const startTag = wrapType === "hint" ? '<hint title="💡 Hint">' : getStartHtmlTagText(wrapType);
        const endTag   = wrapType === "hint" ? '</hint>'               : getEndHtmlTagText(wrapType);

        const anchorStartOriginal = firstChild.originalStart;
        const anchorEndOriginal   = lastChild.originalEnd;    

        result.firstEdit.startInFile = anchorStartOriginal;
        result.firstEdit.endInFile   = anchorStartOriginal;
        result.firstEdit.finalText   = startTag;

        result.secondEdit.startInFile = anchorEndOriginal; 
        result.secondEdit.endInFile   = anchorEndOriginal;
        result.secondEdit.finalText   = endTag;

        const startLen = startTag.length;
        const endLen   = endTag.length;

        
        tree.traverseDepthFirst(node => {
            if (node.originalStart >= anchorEndOriginal) {
            node.originalStart += (startLen + endLen);
            node.originalEnd   += (startLen + endLen);
            } else if (node.originalStart >= anchorStartOriginal) {
            node.originalStart += startLen;
            node.originalEnd   += startLen;
            }
        });

        
        tree.traverseDepthFirst(node => {
            if (node.prosemirrorStart >= step.to) {
            node.prosemirrorStart += 2;
            node.prosemirrorEnd   += 2;
            } else if (node.prosemirrorStart >= step.from) {
            node.prosemirrorStart += 1;
            node.prosemirrorEnd   += 1;
            }
        });

        const wrappedChildren = parent.children.slice(startIdx, endIdx + 1);
        const wrapper = new TreeNode(
            wrapType,
            wrappedChildren[0].originalStart,                    
            wrappedChildren[wrappedChildren.length - 1].originalEnd,
            step.from,                                           
            wrappedChildren[wrappedChildren.length - 1].prosemirrorEnd + 1,
            ""                                                   
        );
        wrappedChildren.forEach(c => wrapper.addChild(c));

        parent.children.splice(startIdx, wrappedChildren.length, wrapper);

        return { result, newTree: tree };
    }

} 
 
