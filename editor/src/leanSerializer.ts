import { TagConfiguration, DocumentSerializer, DefaultTagSerializer, Node } from "@impermeable/waterproof-editor";

type Neighborhood = {nodeAbove: string | null, nodeBelow: string | null}

export class LeanSerializer extends DocumentSerializer {
    private tagSerializer: DefaultTagSerializer;

    constructor(tagConf: TagConfiguration) {
        super();

        this.tagSerializer = new DefaultTagSerializer(tagConf);
    }

    serializeHint(
        hintNode: Node, _parentNode: string | null,
        neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        // if a hint is the first node, we assume that it contains the preamble
        if (neighbors(true).nodeAbove === null) {
            return hintNode.textContent;
        }
        return this.tagSerializer.serializeHint(hintNode);
    }

    serializeCode(
        codeNode: Node, _parentNode: string | null,
        _neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        return this.tagSerializer.serializeCode(codeNode);
    }

    serializeInput(
        inputNode: Node, _parentNode: string | null,
        _neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        return this.tagSerializer.serializeInput(inputNode);
    }

    serializeMarkdown(
        markdownNode: Node, _parentNode: string | null,
        _neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        return this.tagSerializer.serializeMarkdown(markdownNode);
    }

    serializeMath(
        mathNode: Node, _parentNode: string | null,
        _neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        return this.tagSerializer.serializeMath(mathNode);
    }
}
