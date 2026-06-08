/**
 * generate-symbols.mts
 *
 * Merges the hand-curated symbols.json (BASE) with the Lean unicode table,
 * adding any characters from Lean that are not already in the base.
 *
 * Priority order (highest to lowest):
 *   1. symbols.json         - sacred, never modified
 *   2. latex-unicode.json   - all lean labels that also appear in latex are added
 *   3. lean abbreviations   - for applies with no latex match, all lean labels are added
 *
 * All tunable options live in generate-symbols-helpers/generate-symbols.config.mts.
 *
 * Usage:
 *   node generate-symbols.mts                   # merge and write
 *   node generate-symbols.mts --test            # merge, write, then run tests and show reports
 *   node generate-symbols.mts --test --verbose  # also show lean-fallback list and latex{} notice
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

// -- Helpers

/** Build a reverse map: value -> Set<key> from a Map<key, value>. */
function buildReverseMap<K, V>(map: Map<K, V>): Map<V, Set<K>> {
  const reverse = new Map<V, Set<K>>();
  for (const [key, value] of map) {
    if (!reverse.has(value)) reverse.set(value, new Set());
    reverse.get(value)!.add(key);
  }
  return reverse;
}

/**
 * Determines which Unicode block a codepoint belongs to, and thus which symbol panel category it should be in.
 * @param cp The codepoint of the character to categorize.
 * @returns The Unicode block entry for the codepoint, or null if not found.
 */
function blockEntry(cp: number): BlockEntry | null {
  return BLOCKS.find(([[lo, hi]]) => cp >= lo && cp <= hi) ?? null;
}

/**
 * Given a codepoint, determine the natural symbol panel category it belongs to based on its Unicode block
 * @param cp The codepoint of the character to categorize.
 * @returns The natural symbol panel category for the codepoint, or [7, "misc"] if not found.
 */
function categoryFromBlock(cp: number): [number, keyof ShowInPanelConfig] {
  const entry = blockEntry(cp);
  if (!entry) return [7, "misc"];
  const [, cat, key] = entry;
  return [cat, key];
}

/** Compute the symbolPanelCategory for a label+apply pair, or undefined if hidden. */
function computeCategory(label: string, apply: string): number | undefined {
  const cp = apply.codePointAt(0);
  if (cp === undefined) return undefined;
  if (overrides[label] !== undefined) return overrides[label];
  if (/^\\[\^_]/.test(label)) return SHOW_IN_PANEL.scripts ? 5 : undefined;
  const [naturalCat, groupKey] = categoryFromBlock(cp);
  return SHOW_IN_PANEL[groupKey] ? naturalCat : undefined;
}

/** Build a SymbolEntry, attaching symbolPanelCategory only when defined. */
function makeEntry(label: string, apply: string): SymbolEntry {
  const cat = computeCategory(label, apply);
  return cat !== undefined
    ? { label, type: "symbol", apply, symbolPanelCategory: cat }
    : { label, type: "symbol", apply };
}

// -- Step 1: load base symbols

const base: BaseSymbol[] = JSON.parse(fs.readFileSync(BASE, "utf8"));

const baseLabelToEntry = new Map(base.map((s) => [s.label, s]));
const baseApplyToLabels = buildReverseMap(
  new Map(base.map((s) => [s.label, s.apply])),
);

// -- Step 2: load latex-unicode

const latexRaw: Record<string, string> = JSON.parse(
  fs.readFileSync(LATEX, "utf8"),
);

const latexLabelToApply = new Map<string, string>(); // label -> apply (only non-"{}" labels)
const latexBraceLabels: Array<{ label: string; apply: string }> = []; // labels containing "{}" (for --verbose logging)
const multiCodepoint: Array<{ label: string; apply: string }> = [];

for (const [rawLabel, apply] of Object.entries(latexRaw)) {
  const label = rawLabel.startsWith("\\") ? rawLabel : "\\" + rawLabel;
  if (label.includes("{")) {
    latexBraceLabels.push({ label, apply }); // logged with --verbose
    // NOT added!
  } else {
    latexLabelToApply.set(label, apply);
  }
}

// apply -> Set<label>  (only non-"{}"" labels, e.g. \mathbb{A})
const latexApplyToLabels = buildReverseMap(latexLabelToApply);

// -- Step 3: load & normalize lean symbols

const leanRaw: Record<string, string | string[]> = JSON.parse(
  fs.readFileSync(LEAN, "utf8"),
);

const leanAll = new Map<string, string>(); // label -> apply

for (const [key, value] of Object.entries(leanRaw)) {
  const apply = Array.isArray(value) ? value[0] : value;
  if (!apply || apply.includes("$CURSOR")) continue; // Some lean entries have this $CURSOR for things like [$CURSOR], we skip those
  if (apply === "\\" || apply === "\\n") continue; //skip the entries for \ and \n
  const label = key.startsWith("\\") ? key : "\\" + key;
  // multi-codepoint applies like "⋃₀" or "⁻¹" (skip if configured)
  const isMulti = [...apply].length !== 1;
  if (isMulti) multiCodepoint.push({ label, apply });
  if (isMulti && MERGE.skipMultiCodepoint) continue;
  leanAll.set(label, apply);
}

const leanApplyToLabels = buildReverseMap(leanAll);

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

/** Emit symbol entries for a batch of labels and mark them as seen. */
function addEntries(labels: string[], apply: string) {
  seenApplies.add(apply);
  for (const label of labels) {
    if (seenLabels.has(label)) continue;
    seenLabels.add(label);
    symbols.push(makeEntry(label, apply));
  }
}

for (const [apply, leanLabels] of leanApplyToLabels) {
  // Case A: apply already covered by base. Record skipped lean labels for logging, optionally add latex aliases.
  if (seenApplies.has(apply)) {
    const baseLabelsForApply = base
      .filter((s) => s.apply === apply)
      .map((s) => s.label);
    const droppedLabels = [...leanLabels].filter((l) => !seenLabels.has(l));
    if (droppedLabels.length > 0) {
      const latexLabels = latexApplyToLabels.get(apply)
        ? [...latexApplyToLabels.get(apply)!]
        : [];
      report.skippedByApply.set(apply, {
        baseLabels: baseLabelsForApply,
        droppedLabels,
        latexLabels,
      });
    }

    if (MERGE.addLatexIfAlreadyInBase) {
      for (const latexLabel of latexApplyToLabels.get(apply) ?? []) {
        if (seenLabels.has(latexLabel)) continue;
        seenLabels.add(latexLabel);
        latexBaseAliasLabels.add(latexLabel);
        symbols.push(makeEntry(latexLabel, apply));
      }
    }
    continue;
  }

  // Case B: detect label conflicts (lean label already used for a different apply).
  for (const label of leanLabels) {
    const baseEntry = baseLabelToEntry.get(label);
    if (baseEntry && baseEntry.apply !== apply) {
      report.labelConflicts.push({
        label,
        baseApply: baseEntry.apply,
        leanApply: apply,
      });
    }
  }

  const eligibleLeanLabels = [...leanLabels].filter((l) => !seenLabels.has(l));
  if (eligibleLeanLabels.length === 0) continue;

  // Case C: new apply; add via latex match, or fall back to lean-only.
  const latexMatches = eligibleLeanLabels.filter((l) =>
    latexLabelToApply.has(l),
  );

  if (latexMatches.length > 0 && MERGE.addViaLatex) {
    // LaTeX-matched path: no leanLabelStrategy filtering applied here
    // (the latex table is already a quality filter)
    addEntries(latexMatches, apply);
    report.addedViaLatex.push({
      apply,
      addedLabels: latexMatches,
      latexLabels: [...(latexApplyToLabels.get(apply) ?? [])],
      droppedLean: eligibleLeanLabels.filter((l) => !latexMatches.includes(l)),
    });
  } else if (MERGE.addViaLean) {
    // Lean-fallback path
    const { kept, dropped } = filterLeanLabels(
      eligibleLeanLabels,
      MERGE.leanLabelStrategy,
    );
    addEntries(kept, apply);
    report.addedViaLean.push({ apply, addedLabels: kept });
    if (dropped.length > 0) {
      report.filteredLean.push({
        apply,
        keptLabels: kept,
        droppedLabels: dropped,
      });
    }
  }
}

// -- Step 5: Enrich and write output

// Determine which source a lean-added symbol came from (for boost purposes)
const latexAddedLabels = new Set([
  ...report.addedViaLatex.flatMap((r) => r.addedLabels),
  ...latexBaseAliasLabels,
]);

// Pre-build per-apply label lists for alias details.
const finalLabelsByApply = new Map<string, string[]>();
for (const s of symbols) {
  if (!finalLabelsByApply.has(s.apply)) finalLabelsByApply.set(s.apply, []);
  finalLabelsByApply.get(s.apply)!.push(s.label);
}

const enriched: SymbolEntry[] = symbols.map((s) => {
  const allAliases = (finalLabelsByApply.get(s.apply) ?? []).filter(
    (l) => l !== s.label,
  );
  const extras: Partial<Pick<SymbolEntry, "detail" | "boost">> = {};

  if (ENRICHMENT.includeAliasDetails && allAliases.length > 0) {
    extras.detail = ` Also: ${[...allAliases].join(" ")} `;
  }

  if (baseLabelToEntry.has(s.label)) {
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
  multiCodepoint,
  report,
  symbols,
  latexApplyToLabels,
  latexLabelToApply,
  latexBraceLabels,
  leanLabelStrategy: MERGE.leanLabelStrategy,
  VERBOSE,
  base,
  baseApplyToLabels,
  leanApplyToLabels,
});

runTests({
  base,
  enriched,
  report,
  leanAll,
  leanApplyToLabels,
  baseApplyToLabels,
  overrides,
  MERGE,
  fromLean,
});
