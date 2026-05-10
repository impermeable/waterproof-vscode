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

export interface MergeConfig {
    addLatexIfAlreadyInBase: boolean;
    addViaLatex: boolean;
    addViaLean: boolean;
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
    baseLabel: string;
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

export interface LabelConflict {
    label: string;
    baseApply: string;
    leanApply: string;
}

export interface MergeReport {
    skippedByApply: Map<string, SkippedByApplyEntry>;
    addedViaLatex: AddedViaLatexEntry[];
    addedViaLean: AddedViaLeanEntry[];
    labelConflicts: LabelConflict[];
}

// ---------------------------------------------------------------------------
// Shared helper-function signatures (passed via ctx objects)
// ---------------------------------------------------------------------------

export interface AnsiColors {
    reset: string;
    bold: string;
    dim: string;
    green: string;
    yellow: string;
    cyan: string;
    gray: string;
    red: string;
    blue: string;
    magenta: string;
}

export type ColFn            = (color: string, text: string) => string;
export type HintFn           = (msg: string) => string;
export type FmtLabelsFn      = (labels: string[]) => string;
export type GroupByApplyFn   = (items: ReadonlyArray<{ apply: string; label: string }>) => Map<string, string[]>;
export type PairsFn          = (arr: string[]) => [string, string][];
export type CommonPrefixLenFn = (a: string, b: string) => number;

// ---------------------------------------------------------------------------
// Context objects passed to runReports / runTests
// ---------------------------------------------------------------------------

export interface ReportContext {
    report: MergeReport;
    symbols: SymbolEntry[];
    latexApplyToLabels: Map<string, Set<string>>;
    latexLabelToApply: Map<string, string>;
    latexBraceLabels: Array<{ label: string; apply: string }>;
    VERBOSE: boolean;
    C: AnsiColors;
    col: ColFn;
    hint: HintFn;
    fmtLabels: FmtLabelsFn;
    groupByApply: GroupByApplyFn;
    pairs: PairsFn;
    commonPrefixLen: CommonPrefixLenFn;
}

export interface TestContext {
    base: BaseSymbol[];
    symbols: SymbolEntry[];
    enriched: SymbolEntry[];
    report: MergeReport;
    leanAll: Map<string, string>;
    leanApplyToLabels: Map<string, Set<string>>;
    baseApplyToLabel: Map<string, string>;
    overrides: Record<string, number>;
    MERGE: MergeConfig;
    fmtLabels: FmtLabelsFn;
    col: ColFn;
    C: AnsiColors;
    fromLean?: number;
}