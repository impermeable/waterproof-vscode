/**
 * generate-symbols.types.ts
 *
 * Shared types for the generate-symbols pipeline.
 */

// ---------------------------------------------------------------------------
// Symbol entries
// ---------------------------------------------------------------------------

export interface BaseSymbol {
  label: string;
  type: string;
  apply: string;
  symbolPanelCategory?: number;
}

export interface SymbolEntry extends BaseSymbol {
  boost?: number;
  detail?: string;
}

// ---------------------------------------------------------------------------
// Config shapes  (mirrors generate-symbols.config.ts)
// ---------------------------------------------------------------------------

export interface PathsConfig {
  base: string;
  lean: string;
  latex: string;
  output: string;
}

export interface ShowInPanelConfig {
  greekLower: boolean;
  greekUpper: boolean;
  mathLogic: boolean;
  arrows: boolean;
  letterlike: boolean;
  scripts: boolean;
  calligraphic: boolean;
  fraktur: boolean;
  doubleStruck: boolean;
  boldItalic: boolean;
  misc: boolean;
}

/** [[loCodepoint, hiCodepoint], categoryNumber, showInPanelKey] */
export type BlockEntry = [[number, number], number, keyof ShowInPanelConfig];

/**
 * Controls which labels are kept when a Lean character has multiple labels
 * but none of them appear in the LaTeX table (the "lean fallback" group).
 *
 *   "all"             - keep every label (default)
 *   "longest"         - keep only the single longest label (by stem length)
 *   "shortest"        - keep only the single shortest label (by stem length)
 *   "longest_prefix"  - group labels whose stems have a prefix relationship
 *                       (one is a prefix of the other, e.g. \superseteq and
 *                       \superseteqq) and keep the longest within each group;
 *                       labels with no prefix sibling are always kept
 *   "shortest_prefix" - same grouping, but keep the shortest in each group
 */
export type LeanLabelStrategy =
  | "all"
  | "longest"
  | "shortest"
  | "longest_prefix"
  | "shortest_prefix";

export interface MergeConfig {
  addLatexIfAlreadyInBase: boolean;
  addViaLatex: boolean;
  addViaLean: boolean;
  /** Which labels to keep when a lean-only character has multiple labels. */
  leanLabelStrategy: LeanLabelStrategy;
}

export interface EnrichmentConfig {
  baseBoost: number | null;
  latexBoost: number | null;
  leanBoost: number | null;
  includeAliasDetails: boolean;
}

// ---------------------------------------------------------------------------
// Merge-report types
// ---------------------------------------------------------------------------

export interface SkippedByApplyEntry {
  baseLabels: string[];
  droppedLabels: string[];
  latexLabels: string[];
}

export interface AddedViaLatexEntry {
  apply: string;
  addedLabels: string[];
  latexLabels: string[];
  droppedLean: string[];
}

export interface AddedViaLeanEntry {
  apply: string;
  addedLabels: string[];
}

/** Records labels that were dropped by the leanLabelStrategy filter. */
export interface FilteredLeanEntry {
  apply: string;
  keptLabels: string[];
  droppedLabels: string[];
}

export interface LabelConflict {
  label: string;
  baseApply: string;
  leanApply: string;
}

export interface MergeReport {
  skippedByApply: Map<string, SkippedByApplyEntry>;
  addedViaLatex: AddedViaLatexEntry[];
  addedViaLean: AddedViaLeanEntry[];
  /** Characters whose lean-fallback labels were reduced by leanLabelStrategy. */
  filteredLean: FilteredLeanEntry[];
  labelConflicts: LabelConflict[];
}

// ---------------------------------------------------------------------------
// Context objects passed to runReports / runTests
// ---------------------------------------------------------------------------

export interface ReportContext {
  report: MergeReport;
  symbols: SymbolEntry[];
  latexApplyToLabels: Map<string, Set<string>>;
  latexLabelToApply: Map<string, string>;
  latexBraceLabels: Array<{ label: string; apply: string }>;
  leanLabelStrategy: LeanLabelStrategy;
  VERBOSE: boolean;
}

export interface TestContext {
  base: BaseSymbol[];
  enriched: SymbolEntry[];
  report: MergeReport;
  leanAll: Map<string, string>;
  leanApplyToLabels: Map<string, Set<string>>;
  baseApplyToLabel: Map<string, string>;
  overrides: Record<string, number>;
  MERGE: MergeConfig;
  fromLean?: number;
}
