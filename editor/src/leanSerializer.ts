import { DocumentSerializer, DefaultTagSerializer, Node } from "@impermeable/waterproof-editor";
import { tagConfigurationLean } from "./leanFileConfiguration";

type Neighborhood = {nodeAbove: string | null, nodeBelow: string | null}

export class LeanSerializer extends DocumentSerializer {
    private tagSerializer: DefaultTagSerializer;

    constructor() {
        super();

        this.tagSerializer = new DefaultTagSerializer(tagConfigurationLean);
    }

    serializeHint(
        hintNode: Node, _parentNode: string | null,
        neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        // if a hint is the first node, we assume that it contains the preamble
        if (neighbors(true).nodeAbove === null) {
            // TODO: This serialization is used to count newlines, but should not show up in practice.
            // If it does in the future, we need to keep track of the title somehow.
            return hintNode.textContent + "\n#doc (WaterproofGenre) \"Title\" =>\n";
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

    serializeContainer(
        containerNode: Node, _parentNode: string | null,
        _neighbors: (skipNewlines: boolean) => Neighborhood
    ): string {
        return this.tagSerializer.serializeContainer(containerNode);
    }
}
