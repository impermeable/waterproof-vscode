/**
 * generate-symbols.mts
 *
 * Merges the hand-curated symbols.json (BASE) with the Lean unicode table,
 * adding any characters from Lean that are not already in the base.
 *
 * Priority order (highest to lowest):
 *   1. symbols.json  (sacred, never modified)
 *   2. latex-unicode.json  (ALL lean labels that also appear in latex are added)
 *   3. lean abbreviations  (for applies with no latex match, ALL lean labels are added)
 *
 * Categories:
 *   0  Greek lowercase      1  Greek uppercase
 *   2  Math / logic         3  Arrows
 *   4  Letterlike (N R ...)  5  Super / subscripts
 *   6  Calligraphic         7  Misc
 *   99 Hidden (completion-only, not shown in panel)
 *
 * All tunable options live in generate-symbols-helpers/generate-symbols.config.mts.
 *
 * Usage:
 *   node generate-symbols.mts             # merge and write
 *   node generate-symbols.mts --verbose   # also show lean-fallback list and latex{} notice
 *   node generate-symbols.mts --test      # merge, write, then run validation checks
 *   node generate-symbols.mts --verbose --test
 */

import fs from "fs";
import { fileURLToPath } from "url";
import path from "path";

import {
  PATHS,
  SHOW_IN_PANEL,
  BLOCKS,
  OVERRIDES as overrides,
  MERGE,
  ENRICHMENT,
} from "./generate-symbols-helpers/generate-symbols.config.mts";

import { runReports } from "./generate-symbols-helpers/generate-symbols.report.mts";
import { runTests } from "./generate-symbols-helpers/generate-symbols.tests.mts";

import {
  C,
  col,
  filterLeanLabels,
} from "./generate-symbols-helpers/generate-symbols.utils.mts";

import type {
  BaseSymbol,
  SymbolEntry,
  MergeReport,
  BlockEntry,
  ShowInPanelConfig,
} from "./generate-symbols-helpers/generate-symbols.types.mts";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const BASE = path.resolve(__dirname, PATHS.base);
const LEAN = path.resolve(__dirname, PATHS.lean);
const LATEX = path.resolve(__dirname, PATHS.latex);
const OUTPUT = path.resolve(__dirname, PATHS.output);

const TEST = process.argv.includes("--test");
const VERBOSE = process.argv.includes("--verbose");

// -- Unicode block helpers --

function blockEntry(cp: number): BlockEntry | null {
  for (const entry of BLOCKS) {
    const [[lo, hi]] = entry;
    if (cp >= lo && cp <= hi) return entry;
  }
  return null;
}

function categoryFromBlock(cp: number): [number, keyof ShowInPanelConfig] {
  const entry = blockEntry(cp);
  if (!entry) return [7, "misc"];
  const [, cat, key] = entry;
  return [cat, key];
}

/** Compute the symbolPanelCategory for a new lean-added label+apply */
function computeCategory(label: string, apply: string): number | undefined {
  const cp = apply.codePointAt(0);
  if (cp === undefined) return undefined;
  if (overrides[label] !== undefined) return overrides[label];
  if (/^\\[\^_]/.test(label)) return SHOW_IN_PANEL.scripts ? 5 : undefined;
  const [naturalCat, groupKey] = categoryFromBlock(cp);
  return SHOW_IN_PANEL[groupKey] ? naturalCat : undefined;
}

// -- Step 1: load base symbols
const base: BaseSymbol[] = JSON.parse(fs.readFileSync(BASE, "utf8"));

const baseApplyToLabel = new Map<string, string>(
  base.map((s) => [s.apply, s.label]),
);
const baseLabelToEntry = new Map<string, BaseSymbol>(
  base.map((s) => [s.label, s]),
);

// -- Step 2: load latex-unicode

const latexRaw: Record<string, string> = JSON.parse(
  fs.readFileSync(LATEX, "utf8"),
);

const latexApplyToLabels = new Map<string, Set<string>>(); // apply → Set<label>  (only non-{} labels)
const latexLabelToApply = new Map<string, string>(); // label → apply       (only non-{} labels)
const latexBraceLabels: Array<{ label: string; apply: string }> = []; // labels containing {}

for (const [label, apply] of Object.entries(latexRaw)) {
  const normalLabel = label.startsWith("\\") ? label : "\\" + label;
  if (normalLabel.includes("{")) {
    latexBraceLabels.push({ label: normalLabel, apply });
    // intentionally NOT added to latexApplyToLabels or latexLabelToApply
  } else {
    latexLabelToApply.set(normalLabel, apply);
    if (!latexApplyToLabels.has(apply))
      latexApplyToLabels.set(apply, new Set());
    latexApplyToLabels.get(apply)!.add(normalLabel);
  }
}

// -- Step 3: load & normalize lean symbols
const leanJson: Record<string, string | string[]> = JSON.parse(
  fs.readFileSync(LEAN, "utf8"),
);
const leanAll = new Map<string, string>(); // label → apply

for (const [key, value] of Object.entries(leanJson)) {
  const apply = Array.isArray(value) ? value[0] : value;
  if (!apply || apply.includes("$CURSOR")) continue;
  if (apply === "\\" || apply === "\\n") continue;
  if ([...apply].length !== 1) continue;
  const label = key.startsWith("\\") ? key : "\\" + key;
  leanAll.set(label, apply);
}

const leanApplyToLabels = new Map<string, Set<string>>(); // apply → Set<label>
for (const [label, apply] of leanAll) {
  if (!leanApplyToLabels.has(apply)) leanApplyToLabels.set(apply, new Set());
  leanApplyToLabels.get(apply)!.add(label);
}

// -- Step 4: merge
const symbols: SymbolEntry[] = [...base];
const seenLabels = new Set<string>(base.map((s) => s.label));
const seenApplies = new Set<string>(base.map((s) => s.apply));
const latexBaseAliasLabels = new Set<string>();

const report: MergeReport = {
  // apply already covered by symbols.json - only when lean has EXTRA labels
  // { baseLabel, droppedLabels[], latexLabels[] }
  skippedByApply: new Map(),

  // New applies added via latex-matching lean labels (ALL matching labels added)
  // { apply, addedLabels[], latexLabels[], droppedLean[] }
  addedViaLatex: [],

  // New applies added via lean only (ALL lean labels added, no latex match)
  // { apply, addedLabels[] }
  addedViaLean: [],

  // Labels dropped from lean-only characters by the leanLabelStrategy filter
  // { apply, keptLabels[], droppedLabels[] }
  filteredLean: [],

  // Lean label collides with a base label but points to a different character
  labelConflicts: [], // { label, baseApply, leanApply }
};

for (const [apply, leanLabels] of leanApplyToLabels) {
  // -- Case A: apply already in symbols.json
  if (seenApplies.has(apply)) {
    const baseLabel = baseApplyToLabel.get(apply)!;
    const droppedLabels = [...leanLabels].filter((l) => l !== baseLabel);
    if (droppedLabels.length > 0) {
      const latexLabels = latexApplyToLabels.get(apply)
        ? [...latexApplyToLabels.get(apply)!]
        : [];
      report.skippedByApply.set(apply, {
        baseLabel,
        droppedLabels,
        latexLabels,
      });
    }

    // Optionally add extra LaTeX labels for already-covered applies
    if (MERGE.addLatexIfAlreadyInBase) {
      const latexLabels = latexApplyToLabels.get(apply) ?? new Set<string>();
      for (const latexLabel of latexLabels) {
        if (seenLabels.has(latexLabel)) continue;
        seenLabels.add(latexLabel);
        latexBaseAliasLabels.add(latexLabel);
        const cat = computeCategory(latexLabel, apply);
        const entry: SymbolEntry =
          cat !== undefined
            ? {
                label: latexLabel,
                type: "symbol",
                apply,
                symbolPanelCategory: cat,
              }
            : { label: latexLabel, type: "symbol", apply };
        symbols.push(entry);
      }
    }
    continue;
  }

  // -- Case B: detect label conflicts
  for (const leanLabel of leanLabels) {
    if (seenLabels.has(leanLabel)) {
      const baseEntry = baseLabelToEntry.get(leanLabel);
      if (baseEntry && baseEntry.apply !== apply) {
        report.labelConflicts.push({
          label: leanLabel,
          baseApply: baseEntry.apply,
          leanApply: apply,
        });
      }
    }
  }

  const eligibleLeanLabels = [...leanLabels].filter((l) => !seenLabels.has(l));
  if (eligibleLeanLabels.length === 0) continue;

  // -- Case C: add labels
  const latexMatches = eligibleLeanLabels.filter((l) =>
    latexLabelToApply.has(l),
  );
  const latexLabelsForApply = latexApplyToLabels.get(apply)
    ? [...latexApplyToLabels.get(apply)!]
    : [];

  // Labels to actually add as symbol entries this round
  let labelsToAdd: string[];

  if (latexMatches.length > 0 && MERGE.addViaLatex) {
    // LaTeX-matched path: no leanLabelStrategy filtering applied here
    // (the latex table is already a quality filter)
    labelsToAdd = latexMatches;
    report.addedViaLatex.push({
      apply,
      addedLabels: latexMatches,
      latexLabels: latexLabelsForApply,
      droppedLean: eligibleLeanLabels.filter((l) => !latexMatches.includes(l)),
    });
  } else if (latexMatches.length === 0 && MERGE.addViaLean) {
    // Lean-only fallback path: apply the label strategy filter
    const { kept, dropped } = filterLeanLabels(
      eligibleLeanLabels,
      MERGE.leanLabelStrategy,
    );
    labelsToAdd = kept;
    report.addedViaLean.push({ apply, addedLabels: kept });
    if (dropped.length > 0) {
      report.filteredLean.push({
        apply,
        keptLabels: kept,
        droppedLabels: dropped,
      });
    }
  } else if (
    latexMatches.length > 0 &&
    !MERGE.addViaLatex &&
    MERGE.addViaLean
  ) {
    // latex match exists but addViaLatex is off; fall through to lean labels
    const { kept, dropped } = filterLeanLabels(
      eligibleLeanLabels,
      MERGE.leanLabelStrategy,
    );
    labelsToAdd = kept;
    report.addedViaLean.push({ apply, addedLabels: kept });
    if (dropped.length > 0) {
      report.filteredLean.push({
        apply,
        keptLabels: kept,
        droppedLabels: dropped,
      });
    }
  } else {
    continue; // both sources disabled for this apply
  }

  // Emit one symbol entry per label
  seenApplies.add(apply);
  for (const label of labelsToAdd) {
    if (seenLabels.has(label)) continue; // guard against duplicates within batch
    seenLabels.add(label);
    const cat = computeCategory(label, apply);
    const entry: SymbolEntry =
      cat !== undefined
        ? { label, type: "symbol", apply, symbolPanelCategory: cat }
        : { label, type: "symbol", apply };
    symbols.push(entry);
  }
}

// -- Step 5: write output
const baseApplySet = new Set<string>(base.map((s) => s.apply));

// Determine which source a lean-added symbol came from (for boost purposes)
const latexAddedLabels = new Set<string>([
  ...report.addedViaLatex.flatMap((r) => r.addedLabels),
  ...latexBaseAliasLabels,
]);

const finalLabelsByApply = new Map<string, string[]>();
for (const s of symbols) {
  if (!finalLabelsByApply.has(s.apply)) finalLabelsByApply.set(s.apply, []);
  finalLabelsByApply.get(s.apply)!.push(s.label);
}

const enriched: SymbolEntry[] = symbols.map((s) => {
  const allAliases = new Set(finalLabelsByApply.get(s.apply) ?? []);
  allAliases.delete(s.label);

  // Typed explicitly so TypeScript knows which optional fields are valid.
  const extras: Partial<Pick<SymbolEntry, "detail" | "boost">> = {};

  if (ENRICHMENT.includeAliasDetails && allAliases.size > 0) {
    extras.detail = ` Also: ${[...allAliases].join(" ")} `;
  }

  if (baseApplySet.has(s.apply) && base.some((b) => b.label === s.label)) {
    // Base symbol
    if (ENRICHMENT.baseBoost) extras.boost = ENRICHMENT.baseBoost;
  } else if (latexAddedLabels.has(s.label)) {
    // Added via latex alias
    if (ENRICHMENT.latexBoost) extras.boost = ENRICHMENT.latexBoost;
  } else {
    // Added via lean fallback
    if (ENRICHMENT.leanBoost) extras.boost = ENRICHMENT.leanBoost;
  }

  return Object.keys(extras).length ? { ...s, ...extras } : s;
});

fs.writeFileSync(OUTPUT, JSON.stringify(enriched, null, 4), "utf8");

const hidden = symbols.filter(
  (s) => s.symbolPanelCategory === undefined,
).length;
const fromLean = symbols.length - base.length;
console.log(`${col(C.bold, "Base symbols")}   : ${base.length}`);
console.log(`${col(C.bold, "Added from Lean")}: ${fromLean}`);
console.log(
  `${col(C.bold, "Total written")}  : ${symbols.length} (${
    symbols.length - hidden
  } in panel, ${hidden} hidden) -> ${OUTPUT}`,
);

if (!TEST) process.exit(0);

runReports({
  report,
  symbols,
  latexApplyToLabels,
  latexLabelToApply,
  latexBraceLabels,
  leanLabelStrategy: MERGE.leanLabelStrategy,
  VERBOSE,
});

runTests({
  base,
  enriched,
  report,
  leanAll,
  leanApplyToLabels,
  baseApplyToLabel,
  overrides,
  MERGE,
  fromLean,
});
