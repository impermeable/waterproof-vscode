import { TagConfiguration, DocumentSerializer, DefaultTagSerializer, Node } from "@impermeable/waterproof-editor";

export class LeanSerializer extends DocumentSerializer {
    private tagSerializer: DefaultTagSerializer;

    constructor(tagConf: TagConfiguration) {
        super();

        this.tagSerializer = new DefaultTagSerializer(tagConf);
    }

    serializeHint(hintNode: Node, parentNode: string | null, neighbors: (skipNewlines: boolean) => {nodeAbove: string | null, nodeBelow: string | null}): string {
        // if a hint is the first node, we assume that it contains the preamble
        if (neighbors(true).nodeAbove === null) {
            return hintNode.textContent;
        }
        return this.tagSerializer.serializeHint(hintNode);
    }

    serializeCode(codeNode: Node, parentNode: string | null, neighbors: (skipNewlines: boolean) => { nodeAbove: string | null; nodeBelow: string | null; }): string {
        return this.tagSerializer.serializeCode(codeNode);
    }

    serializeInput(inputNode: Node, parentNode: string | null, neighbors: (skipNewlines: boolean) => { nodeAbove: string | null; nodeBelow: string | null; }): string {
        return this.tagSerializer.serializeInput(inputNode);
    }

    serializeMarkdown(markdownNode: Node, parentNode: string | null, neighbors: (skipNewlines: boolean) => { nodeAbove: string | null; nodeBelow: string | null; }): string {
        return this.tagSerializer.serializeMarkdown(markdownNode);
    }

    serializeMath(mathNode: Node, parentNode: string | null, neighbors: (skipNewlines: boolean) => { nodeAbove: string | null; nodeBelow: string | null; }): string {
        return this.tagSerializer.serializeMath(mathNode);
    }
}
