/**
 * generate-symbols.config.mjs
 *
 * All configuration for generate-symbols.mjs lives here.
 * Edit this file to control which symbols are added, how they are boosted,
 * what appears in the symbol panel, and where output is written.
 *
 * After editing, re-run:
 *   node generate-symbols.mjs            # normal run
 *   node generate-symbols.mjs --test     # run + validation suite
 *   node generate-symbols.mjs --verbose  # show full lean-fallback list etc.
 */


// --- File paths ---
// All paths are resolved relative to the directory that contains
// generate-symbols.mjs (i.e. the same __dirname).

export const PATHS = {
    /** Hand-curated base symbol list.  Never modified by the script. */
    base:   "../completions/symbols.json",

    /** Lean unicode abbreviation table (from @leanprover/unicode-input). */
    lean:   "../node_modules/@leanprover/unicode-input/dist/abbreviations.json",

    /** LaTeX-unicode mapping used for alias matching and alias details. 
     *  Symbol mappings in latex-unicode.json are derived from the unicode-math package
     *  https://github.com/latex3/unicode-math  (LPPL 1.3c)
    */
    latex:  "./generate-symbols-helpers/latex2unicode.json",

    /** Merged output file written by the script. */
    output: "../completions/symbols+lean.json",
};


// --- Symbol-panel visibility ---
// Controls whether symbols *added from Lean* are visible in the symbol panel.
//
//   true  -> the symbol is assigned its natural category (visible in panel)
//   false -> symbolPanelCategory is omitted (hidden; completion-only)
//
// Base symbols (symbols.json) are ALWAYS preserved exactly as written and are
// never affected by these flags.

export const SHOW_IN_PANEL = {
    greekLower:   false,   // α β γ δ ε …
    greekUpper:   false,   // Α Β Γ Δ Ε …
    mathLogic:    false,   // ∀ ∃ ∈ ∧ ∨ …
    arrows:       false,   // → ← ⇒ ↦ ⟶ …
    letterlike:   false,   // ℕ ℝ ℤ ℂ ℓ …
    scripts:      false,   // superscripts ⁰¹² … / subscripts ₀₁₂ …
    calligraphic: false,   // script A-Z  (𝒜 ℬ 𝒞 …)
    fraktur:      false,   // fraktur A-Z a-z (𝔄 𝔅 ℭ …)
    doubleStruck: false,   // blackboard bold A-Z (𝔸 𝔹 ℂ …)
    boldItalic:   false,   // bold / italic / sans / mono math letters
    misc:         false,   // everything else
};


// --- Unicode block → natural category table ---
// Used to determine the symbolPanelCategory assigned to a Lean-added symbol
// when the corresponding SHOW_IN_PANEL flag is true.
//
// Format of each entry:  [ [loCodepoint, hiCodepoint], category, showInPanelKey ]
//
// Category numbers:
//   0  Greek lowercase      1  Greek uppercase
//   2  Math / logic         3  Arrows
//   4  Letterlike (ℕ ℝ …)  5  Super / subscripts
//   6  Calligraphic         7  Misc
//
// Ranges listed earlier take priority over ranges listed later when they overlap.

export const BLOCKS = [
    [[0x03B1, 0x03CE], 0, "greekLower"],
    [[0x03D0, 0x03D6], 0, "greekLower"],
    [[0x03F0, 0x03F5], 0, "greekLower"],
    [[0x0391, 0x03A9], 1, "greekUpper"],
    [[0x00B2, 0x00B3], 5, "scripts"],
    [[0x00B9, 0x00B9], 5, "scripts"],
    [[0x2070, 0x209C], 5, "scripts"],
    [[0x2100, 0x214F], 4, "letterlike"],
    [[0x2190, 0x21FF], 3, "arrows"],
    [[0x2B00, 0x2BFF], 3, "arrows"],
    [[0x27F0, 0x27FF], 3, "arrows"],
    [[0x2900, 0x297F], 3, "arrows"],
    [[0x1D49C, 0x1D4CF], 6, "calligraphic"],
    [[0x1D4D0, 0x1D4FF], 6, "calligraphic"],
    [[0x2200, 0x22FF], 2, "mathLogic"],
    [[0x2A00, 0x2AFF], 2, "mathLogic"],
    [[0x27C0, 0x27EF], 2, "mathLogic"],
    [[0x2980, 0x29FF], 2, "mathLogic"],
    // Mathematical Alphanumeric Symbols block (U+1D400-U+1D7FF), split by sub-range,
    // more-specific ranges must come BEFORE the catch-all at the bottom:
    [[0x1D504, 0x1D537], 6, "fraktur"],      // Fraktur + Bold Fraktur A-Z a-z
    [[0x1D538, 0x1D56B], 4, "doubleStruck"], // Double-Struck (blackboard bold) A-Z
    [[0x1D400, 0x1D7FF], 6, "boldItalic"],   // everything else (bold, italic, sans, mono)
];


// --- Per-label category overrides ---
// Force a specific symbolPanelCategory for individual Lean-added labels,
// regardless of their Unicode block or the SHOW_IN_PANEL flags above.
//
// Useful to promote a single symbol into the panel without enabling its whole
// group, or to move a symbol to a different category than its block suggests.
//
// Example:
//   "\\nabla": 2,    // show ∇ in the Math/logic group even if mathLogic is false
//   "\\star":  7,    // show ⋆ in Misc instead of its block's natural category

export const OVERRIDES = {
    // "\\label": categoryNumber,
};


// --- Merge behaviour ---

export const MERGE = {
    /**
     * Add extra LaTeX-alias labels for characters that are already covered by
     * symbols.json
     *
     * false (default): if a character's apply value is already in symbols.json,
     *   keep that base entry unchanged and drop ALL Lean / LaTeX aliases for
     *   that character (current behaviour).
     *
     * true: after preserving the base entry, also add any LaTeX labels for the
     *   same apply that do not collide with an existing label.  The base entry
     *   itself is still never modified.
     */
    addLatexIfAlreadyInBase: false,

    /**
     * Add new symbols whose Lean label matches a LaTeX command
     *
     * true (default): emit entries for Lean labels that also appear in the
     *   LaTeX table (the "✅ New symbols added - latex alias chosen" group).
     *
     * false: skip this entire group.  Combine with addViaLean: false to
     *   produce a base-only output with no Lean symbols at all.
     */
    addViaLatex: true,

    /**
     * Add new symbols that have a Lean label but no LaTeX match
     *
     * true (default): emit entries for Lean labels with no LaTeX counterpart
     *   (the "✅ New symbols added - lean fallback" group).
     *
     * false: skip lean-only symbols.  Useful when you want LaTeX-validated
     *   aliases only.
     */
    addViaLean: true,
};


// --- Output enrichment ---

export const ENRICHMENT = {
    /**
     * Completion-boost score written to the `boost` field of every symbol that
     * comes from symbols.json (the hand-curated base list).
     *
     * Higher values push these entries to the top of completion pop-ups.
     * Set to 0 or null to omit the boost field entirely for base symbols.
     * 
     * Reasoning: hand-curated symbols are probably the most common symbols
     *
     * Default: 5
     */
    baseBoost: 5,

    /**
     * Completion-boost score for symbols added via a LaTeX alias match
     * (the "latex alias chosen" group).
     *
     * Set to 0 or null to omit the boost field for this group.
     *
     * Default: 0  (no boost)
     */
    latexBoost: 0,

    /**
     * Completion-boost score for symbols added via the Lean fallback
     * (no LaTeX match, the "lean fallback" group).
     *
     * Set to 0 or null to omit the boost field for this group.
     *
     * Default: 0  (no boost)
     */
    leanBoost: 0,

    /**
     * Populate the `detail` field on each symbol entry with the full set of
     * known aliases drawn from both the Lean and LaTeX tables?
     *
     * The detail string appears as secondary text in completion pop-ups and
     * lets users discover alternative abbreviations for the same character.
     *
     * true  (default): add detail field when aliases exist.
     * false: never write a detail field.
     */
    includeAliasDetails: true,
};
