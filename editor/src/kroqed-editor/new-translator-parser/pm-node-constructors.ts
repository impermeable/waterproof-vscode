import { TheSchema } from "../kroqed-schema";
import { Node as PNode } from "prosemirror-model";
import { constructBlocks } from "./document-constructor";
import { createInnerHintBlocks, createInnerInputAreaBlocks } from "./block-parsing";
import { createCoqDoc } from "./inner-block-logic/coq-block";

export const text = (content: string) => {
    return TheSchema.text(content);
}

export const markdown = (content: string) => {
    return TheSchema.nodes.markdown.create({}, text(content));
}

export const coqCode = (content: string) => {
    return TheSchema.nodes.coqcode.create({}, text(content));
}

const coqdocRegex = /\(\*\* ([\s\S]*?) \*\)/g;

export const coq = (content: string) => {
    // CAN CONTAIN MATH DISPLAYYYY
    /*
        Coq contains a sequence of coqcode and coqdoc nodes.
        Eg.
        ```coq
        (* `regular' Coq comment *)
        Lemma trivial.
        
        (** * Heading *)   
        (** $ \text{math display} $ *)
        (** % \text{math inline} % *)

        Proof.
        trivial.
        Qed.
        ```
        excluding the ```coq and ``` at the beginning and end. 
    */

    // extract the coqdoc comments from the coq block.
    const coqdocComments = Array.from(content.matchAll(coqdocRegex));

    // Then parse the contents of all the coq doc comments. 
    coqdocComments.map((coqdocComment) => {
        if (coqdocComment.index === undefined) throw new Error("Index of coqdocComment is undefined");
        const range = { from: coqdocComment.index, to: coqdocComment.index + coqdocComment[0].length };
        const blocks = createCoqDoc(coqdocComment[1]);
        console.log(blocks);
    });

    // FIXME: not correct.
    return TheSchema.nodes.coqblock.create({}, coqCode(content));
}

export const coqDown = (content: string) => {
    return TheSchema.nodes.coqdown.create({}, text(content));
}

export const mathDisplay = (content: string) => {
    return TheSchema.nodes.math_display.create({}, text(content));
}

export const inputArea = (content: string) => {
    const childNodes: PNode[] = createInnerInputAreaBlocks(content).map((block) => block.toProseMirror());
    return TheSchema.nodes.input.create({}, childNodes);
}

export const hint = (title: string, content: string) => {
    const childNodes: PNode[] = createInnerHintBlocks(content).map((block) => block.toProseMirror());
    return TheSchema.nodes.hint.create({title}, childNodes);
}