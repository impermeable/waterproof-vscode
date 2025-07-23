import { NodeType, Node as PNode } from "prosemirror-model";

/**
 * Helper function to get all descendants of a node with a given type.
 * @param node The parent node.
 * @param descend Whether to descend into the child nodes.
 * @param type The type of interest.
 * @returns An array containing all the descendant nodes with type `type`, together with their postions in the document.
 */
export function findDescendantsWithType(node: PNode, descend: boolean, type: NodeType): {node: PNode, pos: number}[] {
   // create results array, initially empty.
   const result: {node: PNode, pos: number}[] = [];
   // descend into the child nodes of `node` and append results.
   node.descendants((child, pos) => {
	   if (child.type === type) result.push({node: child, pos});
	   return descend;
   });
   // return the found nodes.
   return result;
}