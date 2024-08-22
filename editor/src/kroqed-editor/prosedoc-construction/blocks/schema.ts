
import { TheSchema } from "../../kroqed-schema";
import { Node as ProseNode } from "prosemirror-model";

// ##### Basic blocks #####

/** Construct basic prosemirror text node. */
export const text = (content: string): ProseNode => {
    return TheSchema.text(content);
}

/** Construct coq markdown prosemirror node. */
export const coqMarkdown = (content: string): ProseNode => {
    return TheSchema.nodes.coqdown.create({}, text(content));
}

/** Construct math display prosemirror node. */
export const mathDisplay = (content: string): ProseNode => {
    return TheSchema.nodes.math_display.create({}, text(content));
}

/** Construct markdown prosemirror node. */
export const markdown = (content: string): ProseNode => {
    return TheSchema.nodes.markdown.create({}, text(content));
}

/** Construct coqcode prosemirror node. */
export const coqCode = (content: string): ProseNode => {
    return TheSchema.nodes.coqcode.create({}, text(content));
}

// ##### With inner blocks #####

/** Construct input area prosemirror node. */
export const inputArea = (childNodes: ProseNode[]): ProseNode => {
    return TheSchema.nodes.input.create({}, childNodes);
}

/** Construct hint prosemirror node. */
export const hint = (title: string, childNodes: ProseNode[]): ProseNode => {
    return TheSchema.nodes.hint.create({title}, childNodes);
}

/** Construct coq prosemirror node. */
export const coqblock = (childNodes: ProseNode[], prePreWhite: string, prePostWhite: string, postPreWhite: string, postPostWhite: string): ProseNode => {
    return TheSchema.nodes.coqblock.create({prePreWhite, prePostWhite, postPreWhite, postPostWhite}, childNodes);
}

/** Construct coqdoc prosemirror node. */
export const coqDoc = (childNodes: ProseNode[], preWhite: string, postWhite: string): ProseNode => {
    return TheSchema.nodes.coqdoc.create({preWhite, postWhite}, childNodes);
}

// ##### Root Node #####
export const root = (childNodes: ProseNode[]): ProseNode => {
    return TheSchema.nodes.doc.create({}, childNodes);
}