// Importing necessary modules from the Codemirror library
import {
    HighlightStyle, LRLanguage, LanguageSupport, delimitedIndent, foldInside, foldNodeProp,
    indentNodeProp, syntaxHighlighting
} from "@codemirror/language"
import { Tag, styleTags, tags as t } from "@lezer/highlight"

// Importing the parser for the Coq language
import { parser } from "./syntax"

// Defining custom tags for specific elements of the Coq language
const customTags = {
    vernacular: Tag.define(),
    gallina: Tag.define()
}

// Highlighting specific elements of the Coq language
export const highlight = HighlightStyle.define([
    { tag: customTags.gallina, color: "#6637dd" },
    { tag: customTags.vernacular, color: "#7872d0" }
])

// Defining the Coq language syntax, highlighting and indentation
export const coqLanguage = LRLanguage.define({
    parser: parser.configure({
        props: [
            indentNodeProp.add({
                Application: delimitedIndent({ closing: ")", align: false })
            }),
            foldNodeProp.add({
                Application: foldInside
            }),
            styleTags({
                Identifier: t.variableName,
                Boolean: t.bool,
                String: t.string,
                BlockComment: t.blockComment,
                "( )": t.paren,
                // extra words
                Gallina: customTags.gallina,
                Vernacular: customTags.vernacular,
            })
        ]
    }),
    languageData: {
        commentTokens: { line: "(*" }
    }
})

export function coq() {
    return new LanguageSupport(coqLanguage)
}

export function coqSyntaxHighlighting() {
    return syntaxHighlighting(highlight);
}
