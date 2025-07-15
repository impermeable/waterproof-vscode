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
export const highlight_dark = HighlightStyle.define([
    { tag: customTags.gallina, color: "#cc00ffff" },
    { tag: customTags.vernacular, color: "#00FF00" }
])

export const highlight_light = HighlightStyle.define([
    { tag: customTags.gallina, color: "#FF0000" },
    { tag: customTags.vernacular, color: "#0000FF" }
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

export function coqSyntaxHighlighting(theme: string) {
    const highlight = theme === "dark" ? highlight_dark : highlight_light;
    return syntaxHighlighting(highlight);
}
