// Importing necessary modules from the Codemirror library
import { Completion, CompletionSource } from "@codemirror/autocomplete"
import {
    HighlightStyle, LRLanguage, LanguageSupport, delimitedIndent, foldInside, foldNodeProp,
    indentNodeProp, syntaxHighlighting
} from "@codemirror/language"
import { Tag, styleTags, tags as t, tagHighlighter } from "@lezer/highlight"

// Importing the parser for the Coq language
import { parser } from "./syntax"

// Defining custom tags for specific elements of the Coq language
let customTags = {
    waterproofTactic: Tag.define(),
    coqSentence: Tag.define(),
}

// Highlighting specific elements of the Coq language
export let highlight = HighlightStyle.define([
    { tag: customTags.waterproofTactic, color: "#0000FF" },
    { tag: customTags.coqSentence, color: "#FF0000" },
    { tag: t.comment, color: "#00FF00" },
])

// Defining the Coq language syntax, highlighting and indentation
export const coqLanguage = LRLanguage.define({
    parser: parser.configure({
        props: [
            // indentNodeProp.add({
            //     Application: delimitedIndent({ closing: ")", align: false })
            // }),
            // foldNodeProp.add({
            //     Application: foldInside
            // }),
            styleTags({
                WaterproofTactic: customTags.waterproofTactic,
                CoqSentence: customTags.coqSentence,
                Comment: t.comment
            })
        ]
    })
})

export function coq() {
    return new LanguageSupport(coqLanguage)
}

export function coqSyntaxHighlighting() {
    return syntaxHighlighting(highlight);
}
