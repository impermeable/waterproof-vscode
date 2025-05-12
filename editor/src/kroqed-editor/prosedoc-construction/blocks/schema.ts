
import { WaterproofSchema } from "../../schema/schema";
import { Node as ProseNode } from "prosemirror-model";

// ##### Basic blocks #####

/** Construct basic prosemirror text node. */
export const text = (content: string): ProseNode => {
    return WaterproofSchema.text(content);
}

/** Construct math display prosemirror node. */
export const mathDisplay = (content: string): ProseNode => {
    return WaterproofSchema.nodes.math_display.create({}, text(content));
}

/** Construct markdown prosemirror node. */
export const markdown = (content: string): ProseNode => {
    return WaterproofSchema.nodes.markdown.create({}, text(content));
}

/** Construct coqcode prosemirror node. */
export const code = (content: string): ProseNode => {
    return WaterproofSchema.nodes.code.create({}, text(content));
}

// ##### With inner blocks #####

/** Construct input area prosemirror node. */
export const inputArea = (childNodes: ProseNode[]): ProseNode => {
    return WaterproofSchema.nodes.input.create({}, childNodes);
}

/** Construct hint prosemirror node. */
export const hint = (title: string, childNodes: ProseNode[]): ProseNode => {
    return WaterproofSchema.nodes.hint.create({title}, childNodes);
}

// ##### Root Node #####
export const root = (childNodes: ProseNode[]): ProseNode => {
    return WaterproofSchema.nodes.doc.create({}, childNodes);
}