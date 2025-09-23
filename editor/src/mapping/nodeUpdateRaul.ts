import { ReplaceAroundStep, ReplaceStep, TagMap } from "@impermeable/waterproof-editor";
import { Tree, TreeNode } from "./Tree";
import { OperationType, ParsedStep } from "./types";
import { DocChange, WrappingDocChange } from "@impermeable/waterproof-editor";
import { getEndHtmlTagText, getStartHtmlTagText, parseFragment } from "./helper-functions";

export class NodeUpdate {

    constructor (private tagMap: TagMap) {}

    /** Used to parse a step that causes nodes to be updated instead of just text */
    nodeUpdate(step: ReplaceStep | ReplaceAroundStep, tree: Tree) : ParsedStep {
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
                result = this.replaceStepDelete(step,tree);
            } else {
                result = this.replaceStepInsert(step,tree);
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

                result = this.replaceAroundStepDelete(step,tree);
            } else if (step.slice.content.childCount == 1 && step.slice.openStart == 0 && step.slice.openEnd == 0) {
                // Error check ReplaceAroundStep insertion
                if (step.gapFrom - step.from > 0 || step.to - step.gapTo > 0 || step.insert != 1) throw new Error(" We only support ReplaceAroundStep that inserts chunk in single node");
                if (tree.findNodeByProsemirrorPosition(step.from) == null || tree.findNodeByProsemirrorPosition(step.to) == null) {
                    throw new Error(" Not a proper wrapping ");
                }
                if(!(step.slice.content.firstChild.type.name == 'hint' || step.slice.content.firstChild.type.name == 'input')) throw new Error(" We only support wrapping in hints or inputs ");

                result = this.replaceAroundStepInsert(step,tree);
            } else {
                throw new Error(" We do not support this type of ReplaceAroundStep");
            }
        }
        return result;        
    }

    replaceStepDelete(step: ReplaceStep, tree: Tree) : ParsedStep {
        //// Determine the in text document change vscode side
        console.log("replace step delete");
        /** The resulting change of this step operation */
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }

        /** Determine the resulting DocChange indices */
        const deletedNode = tree.findNodeByProsemirrorPosition(step.from+1);
        if (!deletedNode) throw new Error("We could not find the correct node");
        const tagStart = getStartHtmlTagText(deletedNode.type).length;
        const tagEnd = getEndHtmlTagText(deletedNode.type).length;
        result.startInFile = deletedNode.innerRange.from- tagStart;
        result.endInFile = deletedNode.innerRange.to + tagEnd;

        //// Update the mapping to reflect the new prosemirror state

        // The offsets that were deleted from the doc needed to update the mappings
        
        const proseStart = deletedNode?.prosemirrorStart ?? 0;
        const proseEnd = deletedNode?.prosemirrorEnd ?? 0;
        const proseOffset = proseStart - proseEnd - 2;
        
        let originalOffset = proseEnd  - proseStart + tagEnd + tagStart;
        originalOffset = -originalOffset;
        
        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart >= proseStart && node.prosemirrorEnd <= proseEnd) {
                // Remove the node from the tree
                const parent = tree.findParent(deletedNode);
                if (parent) {
                    parent.removeChild(deletedNode);
                } else {
                    // maybe it's the root
                    if (tree.root === deletedNode) {
                        // I don't know about this.
                        // tree.root = null; 
                    }
                }
            }
        });

        tree.traverseDepthFirst(node => {
            if (node.prosemirrorStart > proseEnd ) {
                node.innerRange.to += originalOffset; 
                node.innerRange.from += originalOffset;
                node.prosemirrorStart += proseOffset;
                node.prosemirrorEnd += proseOffset;
            } else if (node.prosemirrorStart < proseStart && node.prosemirrorEnd > proseEnd) {
                node.innerRange.to += originalOffset;
                node.prosemirrorEnd += proseOffset;
            }
        });
        let newTree = new Tree;
        newTree = tree;
        //console.log(newTree.root);
        return {result, newTree};
    }

    /** Converts a replace step that is a pure node update to a DocChange */
    replaceStepInsert(step: ReplaceStep, tree: Tree) : ParsedStep {
        const result : DocChange = {
            startInFile: 0,
            endInFile: 0,
            finalText: ""
        }
        let inBetweenText: string = "";
        let proseStart: number;
        let proseEnd: number;
        let textStart: number;
        let textEnd: number;
        let nodeType = step.slice.content.firstChild!.type.name;
        let parentNode = tree.findNodeByProsemirrorPosition(step.from);
        if (!parentNode) throw new Error("We could not find the correct node");
        const final = parseFragment(step.slice.content);
        if (step.slice.content.firstChild!.content.firstChild !== null) inBetweenText = step.slice.content.firstChild!.content.firstChild.textContent;
        result.finalText = final.starttext + inBetweenText + final.endtext;
        const originalOffset = result.finalText.length + final.starttext.length + final.endtext.length;
        const proseOffset = result.finalText.length + final.proseOffset;
        if (tree.root?.children.length == 0) {
            /** Compute the resulting DocChange */
            proseStart = 1;
            proseEnd = 1 + result.finalText.length;
            textStart = 0;
            textEnd = result.finalText.length;
            
        } else {
            /** Compute the resulting DocChange */
            const indent = step.from - parentNode.prosemirrorStart;

            result.startInFile = parentNode.innerRange.from + indent;
            result.endInFile = result.startInFile;
            result.finalText = final.starttext + inBetweenText + final.endtext;

            proseStart = parentNode.prosemirrorStart + indent + final.proseOffset/2;
            proseEnd = proseStart + result.finalText.length;
            textStart = parentNode.innerRange.from + indent + final.tags[0].length;
            textEnd = textStart + result.finalText.length + final.endtext.length - final.tags[final.tags.length-1].length;
        }

        ///Update existing mapping
        tree.traverseDepthFirst((node: TreeNode) => {
            if (node.prosemirrorStart > proseEnd ) {
                node.innerRange.to += originalOffset; 
                node.innerRange.from += originalOffset;
                node.prosemirrorStart += proseOffset;
                node.prosemirrorEnd += proseOffset;
            } else if (node.prosemirrorStart < proseStart && node.prosemirrorEnd > proseEnd) {
                node.innerRange.to += originalOffset;
                node.prosemirrorEnd += proseOffset;
            }
        });
        
        let fragmentNode = step.slice.content.firstChild;
        let index = 1;
        while (fragmentNode) {
            const child = new TreeNode(nodeType, {from: textStart, to: textEnd}, {from: 0, to: 0}, "", proseStart, proseEnd, inBetweenText);
            parentNode.addChild(child);
            parentNode = child;
            fragmentNode = fragmentNode.content.firstChild;
            nodeType = fragmentNode!.type.name;
            textStart = textStart + final.tags[index].length;
            textEnd = textEnd - final.tags[final.tags.length - index - 1].length;
            proseStart = proseStart + 1;
            proseEnd = proseEnd - 1;
            index++;

        }
        let newTree = new Tree;
        newTree = tree;
        return {result, newTree};

    }

    /** Setups the wrapping doc change for the suceeding functions */
    setupWrapper() : WrappingDocChange {
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

    replaceAroundStepDelete(step: ReplaceAroundStep, tree: Tree): ParsedStep {
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

        result.firstEdit.startInFile = wrapper.innerRange.from - startTag.length;
        result.firstEdit.endInFile   = wrapper.innerRange.from;
        result.firstEdit.finalText   = "";

        result.secondEdit.startInFile = wrapper.innerRange.to;
        result.secondEdit.endInFile   = wrapper.innerRange.to + endTag.length;
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

        const cut1 = wrapper.innerRange.from;
        const cut2 = wrapper.innerRange.to;
        const startLen = getStartHtmlTagText(wrapper.type).length;
        const endLen   = getEndHtmlTagText(wrapper.type).length;

        tree.traverseDepthFirst(node => {
            if (node.innerRange.from >= cut2) {
                node.innerRange.from -= (startLen + endLen);
                node.innerRange.to   -= (startLen + endLen);
            } else if (node.innerRange.from >= cut1) {
                node.innerRange.from -= startLen;
                node.innerRange.to   -= startLen;
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



    replaceAroundStepInsert(step: ReplaceAroundStep, tree: Tree): ParsedStep {
        const result: WrappingDocChange = {
            firstEdit:  { startInFile: 0, endInFile: 0, finalText: "" },
            secondEdit: { startInFile: 0, endInFile: 0, finalText: "" },
        };

        const wrapType = step.slice.content.firstChild?.type.name;
        if (!(wrapType === "hint" || wrapType === "input")) {
            throw new Error("We only support wrapping in hints or inputs");
        }

        let parent1: TreeNode;
        const startIdx = -1;
        const endIdx = -1;

        tree.traverseDepthFirst((n: TreeNode) => {
            if (parent1) return; 
            if (!n.children.length) return;
            for (let i = 0; i < n.children.length; i++) {
                if (n.children[i].prosemirrorStart === step.from && n.children[i].prosemirrorEnd   === step.to) {
                    parent1 = n;
                    break;
                }
            }
        });

        const parent:TreeNode = parent1!;

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

        const anchorStartOriginal = firstChild.innerRange.from;
        const anchorEndOriginal   = lastChild.innerRange.to;    

        result.firstEdit.startInFile = anchorStartOriginal;
        result.firstEdit.endInFile   = anchorStartOriginal;
        result.firstEdit.finalText   = startTag;

        result.secondEdit.startInFile = anchorEndOriginal; 
        result.secondEdit.endInFile   = anchorEndOriginal;
        result.secondEdit.finalText   = endTag;

        const startLen = startTag.length;
        const endLen   = endTag.length;

        
        tree.traverseDepthFirst(node => {
            if (node.innerRange.from >= anchorEndOriginal) {
            node.innerRange.from += (startLen + endLen);
            node.innerRange.to   += (startLen + endLen);
            } else if (node.innerRange.from >= anchorStartOriginal) {
            node.innerRange.from += startLen;
            node.innerRange.to   += startLen;
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
            {
                from: wrappedChildren[0].innerRange.from,                    
                to: wrappedChildren[wrappedChildren.length - 1].innerRange.to
            },
            { from: 0, to: 0},
            "",
            step.from,                                           
            wrappedChildren[wrappedChildren.length - 1].prosemirrorEnd + 1,
            ""                                                   
        );
        wrappedChildren.forEach(c => wrapper.addChild(c));

        parent.children.splice(startIdx, wrappedChildren.length, wrapper);

        return { result, newTree: tree };
    }

} 
 
