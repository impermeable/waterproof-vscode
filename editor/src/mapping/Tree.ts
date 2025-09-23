export class TreeNode {
    type: string;
    innerRange: {to: number, from: number};
    range: {to: number, from: number};
    title: string;
    prosemirrorStart: number;
    prosemirrorEnd: number;
    stringContent: string;
    children: TreeNode[];

    constructor(
        type: string,
        innerRange: {to: number, from: number},
        range: {to: number, from: number},
        title: string,
        prosemirrorStart: number,
        prosemirrorEnd: number,
        stringContent: string
    ) {
        this.type = type;
        this.innerRange = innerRange;
        this.range = range;
        this.title = title;
        this.prosemirrorStart = prosemirrorStart;
        this.prosemirrorEnd = prosemirrorEnd;
        this.stringContent = stringContent;
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
        stringContent: string = ""
    ) {
        this.root = new TreeNode(type, innerRange, range, title, prosemirrorStart, prosemirrorEnd, stringContent);
    }

    traverseDepthFirst(callback: (node: TreeNode) => void, node: TreeNode | null = this.root): void {
        if (!node) return;
        callback(node);
        node.children.forEach(child => this.traverseDepthFirst(callback, child));
    }

    traverseBreadthFirst(callback: (node: TreeNode) => void): void {
        if (!this.root) return;
        const queue: TreeNode[] = [this.root];
        while (queue.length > 0) {
            const node = queue.shift();
            if (node) {
                callback(node);
                queue.push(...node.children);
            }
        }
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
