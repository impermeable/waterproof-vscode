// Importing necessary modules from the Codemirror library
import { HighlightStyle, LanguageSupport, LRLanguage } from "@codemirror/language"
import { Tag, styleTags } from "@lezer/highlight"

// Importing the parser for the Coq language
import { parser } from "./syntax"

// Defining custom tags for specific elements of the Coq language
const tags = {
    argument: Tag.define(),
    bullet: Tag.define(),
    comment: Tag.define(),
    definition: Tag.define(),
    focusBrace: Tag.define(),
    lemma: Tag.define(),
    magic: Tag.define(),
    proof: Tag.define(),
    qed: Tag.define(),
    tactic: Tag.define(),
    vernac: Tag.define(),
}

// Highlighting specific elements of the Coq language
export const highlight_dark = HighlightStyle.define([
    { tag: tags.argument, color: "#e9e8e8ff" },
    { tag: tags.bullet, color: "#ff7300ff" },
    { tag: tags.comment, color: "#9ea0b1ff" },
    { tag: tags.definition, color: "#e67065ff" },
    { tag: tags.focusBrace, color: "#ff943cff" },
    { tag: tags.lemma, color: "#e67065ff", textDecoration: "underline"},
    { tag: tags.magic, class: "magic-jump-dark" },
    { tag: tags.tactic, color: "#56b3ffff" },
    { tag: tags.vernac, color: "#e67065ff" },
])

// Highlighting specific elements of the Coq language
export const highlight_light = HighlightStyle.define([
    { tag: tags.argument, color: "#2A2A2Aff" },
    { tag: tags.bullet, color: "#ff7300ff" },
    { tag: tags.comment, color: "#787c99" },
    { tag: tags.definition, color: "#e45649" },
    { tag: tags.focusBrace, color: "#ff7300ff" },
    { tag: tags.lemma, color: "#e45649", textDecoration: "underline" },
    { tag: tags.magic, class: "magic-jump-light" },
    { tag: tags.tactic, color: "#004cf0ff" },
    { tag: tags.vernac, color: "#e45649" },
]);

// Defining the Coq language syntax, highlighting and indentation
const wpLanguage = LRLanguage.define({
    parser: parser.configure({
        props: [
            styleTags({
                // LemmaKeyword
                "Lemma": tags.lemma,
                "Theorem": tags.lemma,
                "Example": tags.lemma,
                // DefinitionKeyword
                "Definition": tags.definition,
                "Inductive": tags.definition,
                "Fixpoint": tags.definition,
                // Other
                "Comment": tags.comment,
                "Argument": tags.argument,
                "p": tags.tactic,
                // Bullet and brace
                "Bullet": tags.bullet,
                "FocusBrace": tags.focusBrace,
                "UnfocusBrace": tags.focusBrace,
                // Vernac
                "Proof": tags.vernac,
                "Qed": tags.vernac,
                "Admitted": tags.vernac,
                "Defined": tags.vernac,
                "RequireImport": tags.vernac,
                "Waterproof": tags.vernac,
                "SetDefault": tags.vernac,
                "OpenScope": tags.vernac,
                "Notation": tags.vernac,
                "Section": tags.vernac,
                "Variable": tags.vernac,
                "Parameter": tags.vernac,
                "Check": tags.vernac,
                "Hypothesis": tags.vernac,
                "Module": tags.vernac,
                "End": tags.vernac,
                // WaterproofTactic
                "Help": tags.tactic,
                "WeArgueByContradiction": tags.tactic,
                "Contradiction": tags.tactic,
                "WeShowBothStatements": tags.tactic,
                "WeShowBothDirections": tags.tactic,
                "WeNowShowTheInductionStep": tags.tactic,
                "Take": tags.tactic,
                "WeNeedToShow": tags.tactic,
                "WeConclude": tags.tactic,
                "Case": tags.tactic,
                "Assume": tags.tactic,
                "ItSufficesToShow": tags.tactic,
                "ItHolds": tags.tactic,
                "WeClaim": tags.tactic,
                "WeUseInductionOn": tags.tactic,
                "Indeed": tags.tactic,
                "Use": tags.tactic,
                "Choose": tags.tactic,
                "WeFirstShowTheBaseCase": tags.tactic,
                "Expand": tags.tactic,
                "Obtain": tags.tactic,
                "ByItHolds": tags.tactic,
                "ByItSufficesToShow": tags.tactic,
                "ByWeConclude": tags.tactic,
                "Define": tags.tactic,
                "Since": tags.tactic,
                "Because": tags.tactic,
                "Either": tags.tactic,
                "WeNeedToVerify": tags.tactic,
                // The tokens that appear in the middle of tactics
                "ArgumentEnd": tags.tactic,
                "It": tags.tactic,
                "As": tags.tactic,
                "Both": tags.tactic,
                "And": tags.tactic,
                "Or": tags.tactic,
                "In": tags.tactic,
                "We": tags.tactic,
                "All": tags.tactic,
                "That": tags.tactic,
                "DefineSymbol": tags.tactic,
                "Magic": tags.magic,
                "SuchAn": tags.tactic,
                "AccordingTo": tags.tactic
            })
        ]
    })
});

export const wpLanguageSupport = new LanguageSupport(wpLanguage);