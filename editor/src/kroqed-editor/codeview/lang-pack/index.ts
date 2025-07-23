// Importing necessary modules from the Codemirror library
import {
    HighlightStyle, LRLanguage, LanguageSupport, delimitedIndent, foldInside, foldNodeProp,
    indentNodeProp, syntaxHighlighting
} from "@codemirror/language"
import { Tag, styleTags, tags as t } from "@lezer/highlight"

// Importing the parser for the Coq language
import { parser } from "./syntax"

// Defining custom tags for specific elements of the Coq language
let customTags = {
    waterproofTactic: Tag.define(),
    tacticInput: Tag.define(),
    takeInput: Tag.define(),
    lemmaStatement: Tag.define(),
    lemma: Tag.define(),
    comment: Tag.define(),
    proofQed: Tag.define()
}

// Highlighting specific elements of the Coq language
export const highlight_dark = HighlightStyle.define([
    { tag: customTags.waterproofTactic, color: "#5EC300" },
    { tag: customTags.tacticInput, color: "#FF0000" },
    { tag: customTags.lemmaStatement, color: "#DB6B16" },
    { tag: customTags.lemma, color: "#FF00F7" },
    { tag: customTags.comment, color: "#0000FF" },
    { tag: customTags.proofQed, color: "#FFE100" },
])

// Highlighting specific elements of the Coq language
export const highlight_light = HighlightStyle.define([
  { tag: customTags.waterproofTactic, color: "#4078f2" },    
  { tag: customTags.tacticInput, color: "#333333" },         
  { tag: customTags.lemmaStatement, color: "#2b3990" },      
  { tag: customTags.lemma, color: "#e45649" },               
  { tag: customTags.comment, color: "#787c99" },           
  { tag: customTags.proofQed, color: "#e45649" },             

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
                TacticInput: customTags.tacticInput,
                Lemma: customTags.lemma,
                Comment: customTags.comment,
                ProofandQed: customTags.proofQed,
                LemmaStatement: customTags.lemmaStatement,
                // Also update each of the middle tokens to match the tactics
                TacticMiddleByOrSince: customTags.waterproofTactic,
                TacticMiddleExpand: customTags.waterproofTactic,
                TacticMiddleObtain: customTags.waterproofTactic,
                TacticMiddleDefine: customTags.waterproofTactic,
                TacticMiddleBecauseFirst: customTags.waterproofTactic,
                TacticMiddleBecauseSecond: customTags.waterproofTactic,
                TacticMiddleEither: customTags.waterproofTactic
            })
        ]
    })
})

export function coq() {
    return new LanguageSupport(coqLanguage)
}

export function coqSyntaxHighlighting(theme: string) {
    const highlight = theme === "dark" ? highlight_dark : highlight_light;
    return syntaxHighlighting(highlight);
}
