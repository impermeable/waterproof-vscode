import { Block } from "./blocks";
import { root } from "./blocks/schema";
import { Node as ProseNode } from "prosemirror-model";

// Construct the prosemirror document from the top level blocks.
export function constructDocument(blocks: Block[]): ProseNode {
    const documentContent: ProseNode[] = blocks.map(block => block.toProseMirror());
    return root(documentContent);
}
