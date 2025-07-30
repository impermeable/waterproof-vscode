import { schema } from "prosemirror-markdown";
import { Schema } from "prosemirror-model";
import { mathInlineSpec } from "../../math-integration";

/**
 * The schema in use to render markdown. 
 * Consists of the default prosemirror-markdown schema augmented with the
 * prosemirror-math `math_inline` nodes.
 */
export const markdownRenderingSchema = new Schema({
    nodes: schema.spec.nodes.update("math_inline", mathInlineSpec),
    marks: schema.spec.marks
});