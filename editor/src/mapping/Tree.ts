export class TreeNode {
    /** The type of this node, should be in the WaterproofSchema schema */
    type: string;
    /** The inner range of the node, that is, the range of the content */
    innerRange: {to: number, from: number};
    /** The outer range of the node, that is, the range of the content including possible tags */
    range: {to: number, from: number};
    /** The title of a node, only relevant for hint nodes */
    title: string;
    /** The computed start position in ProseMirror, this is the prosemirror position at which the content starts. 
     * Thus, for nodes with content this includes a +1 due to stepping in to the node. 
     * For newlines, there is no content, so the start points directly before the newline.
     */
    prosemirrorStart: number;
    /** The computed end position in ProseMirror */
    prosemirrorEnd: number;
    /** Potential children of this tree node */
    children: TreeNode[];

    constructor(
        type: string,
        innerRange: {to: number, from: number},
        range: {to: number, from: number},
        title: string,
        prosemirrorStart: number,
        prosemirrorEnd: number
    ) {
        this.type = type;
        this.innerRange = innerRange;
        this.range = range;
        this.title = title;
        this.prosemirrorStart = prosemirrorStart;
        this.prosemirrorEnd = prosemirrorEnd;
        this.children = [];
    }

    addChild(child: TreeNode): void {
        this.children.push(child);
        // Sort children by originalStart to maintain order
        this.children.sort((a, b) => a.innerRange.from - b.innerRange.from);
    }

    removeChild(child: TreeNode): void {
        this.children = this.children.filter(c => c != child);
    }

    shiftCloseOffsets(offset: number, offsetProsemirror?: number): void {
        this.prosemirrorEnd += offsetProsemirror !== undefined ? offsetProsemirror : offset;
        this.innerRange.to += offset;
        this.range.to += offset;
    }

    shiftOffsets(offset: number, offsetProsemirror?: number): void {
        console.log("test", offset)
        this.prosemirrorStart += offsetProsemirror !== undefined ? offsetProsemirror : offset;
        this.prosemirrorEnd += offsetProsemirror !== undefined ? offsetProsemirror : offset;
        this.innerRange.from += offset;
        this.innerRange.to += offset;
        this.range.from += offset;
        this.range.to += offset;
    }

    traverseDepthFirst(callback: (node: TreeNode) => void): void {
        callback(this);
        this.children.forEach(child => child.traverseDepthFirst(callback));
    }
}

export class Tree {
    root: TreeNode;
    
    constructor(
        type: string = "",
        innerRange: {from: number, to: number} = {from: 0, to: 0},
        range: {from: number, to: number} = {from: 0, to: 0},
        title: string = "",
        prosemirrorStart: number = 0,
        prosemirrorEnd: number = 0,
    ) {
        this.root = new TreeNode(type, innerRange, range, title, prosemirrorStart, prosemirrorEnd);
    }

    traverseDepthFirst(callback: (node: TreeNode) => void, node: TreeNode = this.root): void {
        callback(node);
        node.children.forEach(child => this.traverseDepthFirst(callback, child));
    }

    traverseBreadthFirst(callback: (node: TreeNode) => void): void {
        const queue: TreeNode[] = [this.root];
        while (queue.length > 0) {
            const node = queue.shift();
            if (node) {
                callback(node);
                queue.push(...node.children);
            }
        }
    }

    // Finds the highest (closest to root) node that contains the given prosemirror position
    findHighestContainingNode(pos: number, node: TreeNode = this.root): TreeNode {
        if (pos < node.prosemirrorStart || pos > node.prosemirrorEnd) {
            throw new Error("Position out of bounds");
        }
        for (const child of node.children) {
            if (pos >= child.prosemirrorStart && pos <= child.prosemirrorEnd) {
                return this.findHighestContainingNode(pos, child);
            }
        }
        return node;
    }


    findParent(target: TreeNode, node: TreeNode | null = this.root, parent: TreeNode | null = null): TreeNode | null {
        if (!node) return null;
        if (node === target) return parent;
        for (const child of node.children) {
            const result = this.findParent(target, child, node);
            if (result) return result;
        }
        return null;
    }

    findNodeByOriginalPosition(pos: number, node: TreeNode | null = this.root): TreeNode | null {
        if (!node) return null;
        if (pos >= node.innerRange.from && pos <= node.innerRange.to) {
            for (const child of node.children) {
                const result = this.findNodeByOriginalPosition(pos, child);
                if (result) return result;
            }
            return node;
        }
        return null;
    }

    findNodeByProsemirrorPosition(pos: number, node: TreeNode | null = this.root): TreeNode | null {
        if (!node) return null;
        if (pos >= node.prosemirrorStart && pos <= node.prosemirrorEnd) {
            for (const child of node.children) {
                const result = this.findNodeByProsemirrorPosition(pos, child);
                if (result) return result;
            }
            return node;
        }
        return null;
    }

    findNodeByProsePos(pos: number, node: TreeNode | null = this.root): TreeNode | null {
        if (!node) return null;
        if (pos < node.prosemirrorStart || pos > node.prosemirrorEnd) return null;

        // Binary search among children
        let left = 0;
        let right = node.children.length - 1;
        while (left <= right) {
            const mid = Math.floor((left + right) / 2);
            const child = node.children[mid];
            if (pos < child.prosemirrorStart) {
                right = mid - 1;
            } else if (pos > child.prosemirrorEnd) {
                left = mid + 1;
            } else {
                // Found a child that contains pos, recurse
                return this.findNodeByProsePos(pos, child);
            }
        }
        // If no child contains pos, return current node
        return node;
    }

    insertByPosition(newNode: TreeNode): boolean {
        if (!this.root) return false;
        
        for (const rootNode of this.root.children) {
            if (newNode.innerRange.from >= rootNode.innerRange.from && newNode.innerRange.to <= rootNode.innerRange.to) {
                rootNode.addChild(newNode);
                return true;
            }
        }
        this.root.addChild(newNode);
        return true;
    }
}
