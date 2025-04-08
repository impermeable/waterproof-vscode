class TreeNode<T> {
    value: T;
    children: TreeNode<T>[];

    constructor(value: T) {
        this.value = value;
        this.children = [];
    }

    addChild(child: TreeNode<T>): void {
        this.children.push(child);
    }

    removeChild(child: TreeNode<T>): void {
        this.children = this.children.filter(c => c !== child);
    }
}

export class Tree<T> {
    root: TreeNode<T> | null;

    constructor(value?: T) {
        this.root = value !== undefined ? new TreeNode(value) : null;
    }

    traverseDepthFirst(callback: (node: TreeNode<T>) => void, node: TreeNode<T> | null = this.root): void {
        if (!node) return;
        callback(node);
        node.children.forEach(child => this.traverseDepthFirst(callback, child));
    }

    traverseBreadthFirst(callback: (node: TreeNode<T>) => void): void {
        if (!this.root) return;
        const queue: TreeNode<T>[] = [this.root];
        while (queue.length > 0) {
            const node = queue.shift();
            if (node) {
                callback(node);
                queue.push(...node.children);
            }
        }
    }
}
