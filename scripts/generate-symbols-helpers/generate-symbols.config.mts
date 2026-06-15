/**
 * generate-symbols.config.ts
 *
 * All configuration for generate-symbols.ts.
 * After editing, run:
 *   node --import tsx/esm generate-symbols.ts                   # normal run
 *   node --import tsx/esm generate-symbols.ts --test            # run + validation suite
 *   node --import tsx/esm generate-symbols.ts --test --verbose  # show full lean-fallback list etc.
 */

import type {
  PathsConfig,
  ShowInPanelConfig,
  BlockEntry,
  MergeConfig,
  EnrichmentConfig,
} from "./generate-symbols.types.mts";

// --- File paths (resolved relative to generate-symbols.mts) ---

export const PATHS: PathsConfig = {
  /** Hand-curated base symbol list.  Never modified by the script. */
  base: "../completions/symbols.json",

  /** Lean unicode abbreviation table (from @leanprover/unicode-input). */
  lean: "../node_modules/@leanprover/unicode-input/dist/abbreviations.json",

  /** LaTeX-unicode mapping used for alias matching and alias details.
   *  Symbol mappings in latex-unicode.json are derived from the unicode-math package
   *  https://github.com/latex3/unicode-math  (LPPL 1.3c)
   */
  latex: "./generate-symbols-helpers/latex2unicode.json",

  /** Merged output file written by the script. */
  output: "../completions/symbols+lean.json",
};

// --- Symbol-panel visibility ---
// Controls lean-added symbols only; base symbols are always preserved as-is.
// true  -> assign natural category (visible in panel)
// false -> omit symbolPanelCategory (hidden; completion-only)

// Base symbols (symbols.json) are ALWAYS preserved exactly as written and are
// never affected by these flags.

export const SHOW_IN_PANEL: ShowInPanelConfig = {
  greekLower: false, // α β γ …
  greekUpper: false, // Α Β Γ …
  mathLogic: false, // ∀ ∃ ∈ ∧ …
  arrows: false, // → ← ⇒ ↦ …
  letterlike: false, // ℕ ℝ ℤ …
  scripts: false, // ⁰¹² … / ₀₁₂ …
  calligraphic: false, // 𝒜 ℬ 𝒞 …
  fraktur: false, // 𝔄 𝔅 ℭ …
  doubleStruck: false, // 𝔸 𝔹 ℂ …
  boldItalic: false, // bold / italic / sans / mono math letters
  misc: false,
};

// --- Unicode block → natural category ---
// Format: [ [lo, hi], category, showInPanelKey ]
// Categories: 0 Greek lower  1 Greek upper  2 Math/logic  3 Arrows
//             4 Letterlike   5 Scripts      6 Calligraphic 7 Misc
// Earlier entries take priority on overlap.

export const BLOCKS: BlockEntry[] = [
  [[0x03b1, 0x03ce], 0, "greekLower"],
  [[0x03d0, 0x03d6], 0, "greekLower"],
  [[0x03f0, 0x03f5], 0, "greekLower"],
  [[0x0391, 0x03a9], 1, "greekUpper"],
  [[0x00b2, 0x00b3], 5, "scripts"],
  [[0x00b9, 0x00b9], 5, "scripts"],
  [[0x2070, 0x209c], 5, "scripts"],
  [[0x2100, 0x214f], 4, "letterlike"],
  [[0x2190, 0x21ff], 3, "arrows"],
  [[0x2b00, 0x2bff], 3, "arrows"],
  [[0x27f0, 0x27ff], 3, "arrows"],
  [[0x2900, 0x297f], 3, "arrows"],
  [[0x1d49c, 0x1d4cf], 6, "calligraphic"],
  [[0x1d4d0, 0x1d4ff], 6, "calligraphic"],
  [[0x2200, 0x22ff], 2, "mathLogic"],
  [[0x2a00, 0x2aff], 2, "mathLogic"],
  [[0x27c0, 0x27ef], 2, "mathLogic"],
  [[0x2980, 0x29ff], 2, "mathLogic"],
  [[0x1d504, 0x1d537], 6, "fraktur"],
  [[0x1d538, 0x1d56b], 4, "doubleStruck"],
  [[0x1d400, 0x1d7ff], 6, "boldItalic"],
];

// --- Per-label category overrides ---
// Force a symbolPanelCategory for specific labels, ignoring block + SHOW_IN_PANEL.
// Example: "\\nabla": 2  (show ∇ in Math/logic even if mathLogic is false)

export const OVERRIDES: Record<string, number> = {
  // "\\label": categoryNumber,
};

// --- Merge behaviour ---

export const MERGE: MergeConfig = {
  /**
   * Also add LaTeX alias labels for characters already in symbols.json.
   * The base entry itself is never modified; only non-colliding aliases are added.
   * Default: false
   */
  addLatexIfAlreadyInBase: false,

  /**
   * When a Lean label matches a LaTeX command, treat it as a LaTeX-validated
   * entry: skip the {@link MergeConfig.leanLabelStrategy} filter and include
   * all matching labels.
   * Set false to route these entries through the normal Lean fallback path
   * (subject to {@link MergeConfig.leanLabelStrategy}) instead.
   * Default: true
   */
  addViaLatex: true,

  /**
   * Add new symbols with a Lean label but no LaTeX match.
   * Set false to restrict output to LaTeX-validated aliases only.
   * Default: true
   * Reasoning: this ensures that every symbol from Lean is added,
   * even if it does not appear in the LaTeX table.
   */
  addViaLean: true,

  /**
   * Which labels to keep when a lean-only character has multiple Lean labels.
   *   "all"             - keep all labels
   *   "longest"         - keep only the longest stem
   *   "shortest"        - keep only the shortest stem
   *   "longest_prefix"  - group by prefix relationship, keep longest per group
   *   "shortest_prefix" - group by prefix relationship, keep shortest per group
   * Has no effect on addViaLatex entries (already filtered by the LaTeX table).
   *
   * Reasoning: Symbols that are prefixes of longer ones are often just short-hand for longer
   * symbols. In our auto-complete system, all it does is generally add clutter.
   *
   * Why longest_prefix instead of just longest? Some characters like \times and \vectorproduct
   * resolve to the same symbol, yet they server in different contexts.
   */
  leanLabelStrategy: "longest_prefix",

  /**
   * Skip Lean entries whose apply value is more than one Unicode codepoint
   * (e.g. "⋃₀", "⁻¹").  Set true to exclude them from the merged output.
   * Default: true
   * Reasoning: they clutter up the auto-complete with characters that can be compoesd from simpler ones
   */
  skipMultiCodepoint: true,
};

// --- Output enrichment ---

export const ENRICHMENT: EnrichmentConfig = {
  /** Boost for hand-curated base symbols. 0/null to omit. Default: 5
   * Reasoning: Hand-curated symbols are typically the most used ones.
   */
  baseBoost: 5,

  /** Boost for symbols added via LaTeX alias. 0/null to omit. Default: 0 */
  latexBoost: 0,

  /** Boost for symbols added via Lean fallback. 0/null to omit. Default: 0 */
  leanBoost: 0,

  /**
   * Populate the `detail` field with known aliases from Lean + LaTeX tables.
   * Aliases appear as secondary text in completion pop-ups.
   * Default: true
   */
  includeAliasDetails: true,
};
