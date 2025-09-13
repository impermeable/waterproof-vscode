export class TreeNode {
    type: string;
    originalStart: number;
    originalEnd: number;
    prosemirrorStart: number;
    prosemirrorEnd: number;
    stringContent: string;
    children: TreeNode[];

    constructor(
        type: string,
        originalStart: number,
        originalEnd: number,
        prosemirrorStart: number,
        prosemirrorEnd: number,
        stringContent: string
    ) {
        this.type = type;
        this.originalStart = originalStart;
        this.originalEnd = originalEnd;
        this.prosemirrorStart = prosemirrorStart;
        this.prosemirrorEnd = prosemirrorEnd;
        this.stringContent = stringContent;
        this.children = [];
    }

    addChild(child: TreeNode): void {
        this.children.push(child);
    }

    removeChild(child: TreeNode): void {
        this.children = this.children.filter(c => c != child);
    }

}

export class Tree {
    root: TreeNode | null;
    
    constructor(
        type: string = "",
        originalStart: number = 0,
        originalEnd: number = 0,
        prosemirrorStart: number = 0,
        prosemirrorEnd: number = 0,
        stringContent: string = ""
    ) {
        this.root = new TreeNode(type, originalStart, originalEnd, prosemirrorStart, prosemirrorEnd, stringContent);
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
        if (pos >= node.originalStart && pos < node.originalEnd) {
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

}
