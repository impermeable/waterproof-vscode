import { TheSchema } from "../kroqed-schema";

export const text = (content: string) => {
    return TheSchema.text(content);
}

export const markdown = (content: string) => {
    return TheSchema.nodes.markdown.create({}, text(content));
}

export const coqCode = (content: string) => {
    return TheSchema.nodes.coqcode.create({}, text(content));
}

export const coq = (content: string) => {
    // FIXME: not correct.
    return TheSchema.nodes.coq.create({}, coqCode(content));
}

export const coqDown = (content: string) => {
    return TheSchema.nodes.coqdown.create({}, text(content));
}

export const mathDisplay = (content: string) => {
    return TheSchema.nodes.math_display.create({}, text(content));
}