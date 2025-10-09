import { constructDocument, DocumentSerializer, Mapping } from "@impermeable/waterproof-editor";
import { vFileParser } from "../../editor/src/document-construction/vFile";
import { tagConfigurationV } from "../../editor/src/vFileConfiguration";

test("blockAt for sample .v file", () => {
    const doc = "(** * Test *)\nCompute 3 + 3.\n(* begin input *)\nThis is some input.\n(* end input *)\n(** Another *)";

    const blocks = vFileParser(doc);

    const mapping = new Mapping(blocks, 0, tagConfigurationV, new DocumentSerializer(tagConfigurationV));
    const proseDoc = constructDocument(blocks);
    const tree = mapping.getMapping();

    tree.traverseDepthFirst(treeNode => {
        if (treeNode === tree.root) return;

        expect(proseDoc.nodeAt(treeNode.pmRange.from)?.type.name).toBe(treeNode.type);
    });
});