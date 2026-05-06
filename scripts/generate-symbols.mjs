/**
 * generate-symbols.mjs
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
 * All tunable options live in generate-symbols.config.mjs.
 *
 * Usage:
 *   node generate-symbols.mjs             # merge and write
 *   node generate-symbols.mjs --verbose   # also show lean-fallback list and latex{} notice
 *   node generate-symbols.mjs --test      # merge, write, then run validation checks
 *   node generate-symbols.mjs --verbose --test
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
} from "./config.generate-symbols.mjs";

import { runReports } from "./generate-symbols-helpers/report.generate-symbols.mjs";
import { runTests } from "./generate-symbols-helpers/test.generate-symbols.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const BASE = path.resolve(__dirname, PATHS.base);
const LEAN = path.resolve(__dirname, PATHS.lean);
const LATEX = path.resolve(__dirname, PATHS.latex);
const OUTPUT = path.resolve(__dirname, PATHS.output);

const TEST = process.argv.includes("--test");
const VERBOSE = process.argv.includes("--verbose");

// -- Unicode block helpers --

function blockEntry(cp) {
  for (const entry of BLOCKS) {
    const [[lo, hi]] = entry;
    if (cp >= lo && cp <= hi) return entry;
  }
  return null;
}

function categoryFromBlock(cp) {
  const entry = blockEntry(cp);
  if (!entry) return [7, "misc"];
  const [, cat, key] = entry;
  return [cat, key];
}

// -- ANSI color helpers --
const C = {
  reset: "\x1b[0m",
  bold: "\x1b[1m",
  dim: "\x1b[2m",
  green: "\x1b[32m",
  yellow: "\x1b[33m",
  cyan: "\x1b[36m",
  gray: "\x1b[90m",
  red: "\x1b[31m",
  blue: "\x1b[34m",
  magenta: "\x1b[35m",
};

function col(color, text) {
  return `${color}${text}${C.reset}`;
}
function hint(msg) {
  return col(C.dim, `(${msg})`);
}

// -- Helpers --

/** Common prefix length, ignoring leading backslash */
function commonPrefixLen(a, b) {
  const sa = a.startsWith("\\") ? a.slice(1) : a;
  const sb = b.startsWith("\\") ? b.slice(1) : b;
  let i = 0;
  while (i < sa.length && i < sb.length && sa[i] === sb[i]) i++;
  return i;
}

/** Format labels as a comma-separated string */
function fmtLabels(labels) {
  return labels.join(", ");
}

/** Group an array of {apply, label} items by apply, collecting labels */
function groupByApply(items) {
  const map = new Map();
  for (const { apply, label } of items) {
    if (!map.has(apply)) map.set(apply, []);
    map.get(apply).push(label);
  }
  return map;
}

/** Returns all pairs from an array */
function pairs(arr) {
  const result = [];
  for (let i = 0; i < arr.length; i++)
    for (let j = i + 1; j < arr.length; j++) result.push([arr[i], arr[j]]);
  return result;
}

/** Compute the symbolPanelCategory for a new lean-added label+apply */
function computeCategory(label, apply) {
  const cp = apply.codePointAt(0);
  if (overrides[label] !== undefined) return overrides[label];
  if (/^\\[\^_]/.test(label)) return SHOW_IN_PANEL.scripts ? 5 : undefined;
  const [naturalCat, groupKey] = categoryFromBlock(cp);
  return SHOW_IN_PANEL[groupKey] ? naturalCat : undefined;
}

// -- Step 1: load base symbols
const base = JSON.parse(fs.readFileSync(BASE, "utf8"));

const baseApplyToLabel = new Map(base.map((s) => [s.apply, s.label]));
const baseLabelToEntry = new Map(base.map((s) => [s.label, s]));

// -- Step 2: load latex-unicode
const latexRaw = JSON.parse(fs.readFileSync(LATEX, "utf8"));
const latexApplyToLabels = new Map(); // apply → Set<label>  (only non-{} labels)
const latexLabelToApply = new Map(); // label → apply       (only non-{} labels)
const latexBraceLabels = []; // { label, apply }    (labels containing {})

for (const [label, apply] of Object.entries(latexRaw)) {
  const normalLabel = label.startsWith("\\") ? label : "\\" + label;
  if (normalLabel.includes("{")) {
    latexBraceLabels.push({ label: normalLabel, apply });
    if (!latexApplyToLabels.has(apply))
      latexApplyToLabels.set(apply, new Set());
    // intentionally NOT added to latexLabelToApply - won't be chosen as a lean label
  } else {
    latexLabelToApply.set(normalLabel, apply);
    if (!latexApplyToLabels.has(apply))
      latexApplyToLabels.set(apply, new Set());
    latexApplyToLabels.get(apply).add(normalLabel);
  }
}

// -- Step 3: load & normalize lean symbols
const leanJson = JSON.parse(fs.readFileSync(LEAN, "utf8"));
const leanAll = new Map(); // label → apply

for (const [key, value] of Object.entries(leanJson)) {
  const apply = Array.isArray(value) ? value[0] : value;
  if (!apply || apply.includes("$CURSOR")) continue;
  if (apply === "\\" || apply === "\\n") continue;
  if ([...apply].length !== 1) continue;
  const label = key.startsWith("\\") ? key : "\\" + key;
  leanAll.set(label, apply);
}

const leanApplyToLabels = new Map(); // apply → Set<label>
for (const [label, apply] of leanAll) {
  if (!leanApplyToLabels.has(apply)) leanApplyToLabels.set(apply, new Set());
  leanApplyToLabels.get(apply).add(label);
}

// -- Step 4: merge
const symbols = [...base];
const seenLabels = new Set(base.map((s) => s.label));
const seenApplies = new Set(base.map((s) => s.apply));

const report = {
  // apply already covered by symbols.json - only when lean has EXTRA labels
  // { baseLabel, droppedLabels[], latexLabels[] }
  skippedByApply: new Map(),

  // New applies added via latex-matching lean labels (ALL matching labels added)
  // { apply, addedLabels[], latexLabels[], droppedLean[] }
  addedViaLatex: [],

  // New applies added via lean only (ALL lean labels added, no latex match)
  // { apply, addedLabels[] }
  addedViaLean: [],

  // Lean label collides with a base label but points to a different character
  labelConflicts: [], // { label, baseApply, leanApply }
};

for (const [apply, leanLabels] of leanApplyToLabels) {
  // -- Case A: apply already in symbols.json
  if (seenApplies.has(apply)) {
    const baseLabel = baseApplyToLabel.get(apply);
    const droppedLabels = [...leanLabels].filter((l) => l !== baseLabel);
    if (droppedLabels.length > 0) {
      const latexLabels = latexApplyToLabels.get(apply)
        ? [...latexApplyToLabels.get(apply)]
        : [];
      report.skippedByApply.set(apply, {
        baseLabel,
        droppedLabels,
        latexLabels,
      });
    }

    // Optionally add extra LaTeX labels for already-covered applies
    if (MERGE.addLatexIfAlreadyInBase) {
      const latexLabels = latexApplyToLabels.get(apply) ?? new Set();
      for (const latexLabel of latexLabels) {
        if (seenLabels.has(latexLabel)) continue;
        seenLabels.add(latexLabel);
        const cat = computeCategory(latexLabel, apply);
        const entry =
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
    ? [...latexApplyToLabels.get(apply)]
    : [];

  // Labels to actually add as symbol entries this round
  let labelsToAdd;
  let source; // "latex" | "lean"

  if (latexMatches.length > 0 && MERGE.addViaLatex) {
    labelsToAdd = latexMatches;
    source = "latex";
    report.addedViaLatex.push({
      apply,
      addedLabels: latexMatches,
      latexLabels: latexLabelsForApply,
      droppedLean: eligibleLeanLabels.filter((l) => !latexMatches.includes(l)),
    });
  } else if (latexMatches.length === 0 && MERGE.addViaLean) {
    labelsToAdd = eligibleLeanLabels;
    source = "lean";
    report.addedViaLean.push({
      apply,
      addedLabels: eligibleLeanLabels,
    });
  } else if (
    latexMatches.length > 0 &&
    !MERGE.addViaLatex &&
    MERGE.addViaLean
  ) {
    // latex match exists but addViaLatex is off; fall through to lean labels
    labelsToAdd = eligibleLeanLabels;
    source = "lean";
    report.addedViaLean.push({
      apply,
      addedLabels: eligibleLeanLabels,
    });
  } else {
    continue; // both sources disabled for this apply
  }

  // Emit one symbol entry per label
  seenApplies.add(apply);
  for (const label of labelsToAdd) {
    if (seenLabels.has(label)) continue; // guard against duplicates within batch
    seenLabels.add(label);
    const cat = computeCategory(label, apply);
    const entry =
      cat !== undefined
        ? { label, type: "symbol", apply, symbolPanelCategory: cat }
        : { label, type: "symbol", apply };
    symbols.push(entry);
  }
}

// -- Step 5: write output
const baseApplySet = new Set(base.map((s) => s.apply));

// Determine which source a lean-added symbol came from (for boost purposes)
const latexAddedLabels = new Set(
  report.addedViaLatex.flatMap((r) => r.addedLabels),
);

const finalLabelsByApply = new Map();
for (const s of symbols) {
  if (!finalLabelsByApply.has(s.apply)) finalLabelsByApply.set(s.apply, []);
  finalLabelsByApply.get(s.apply).push(s.label);
}

const enriched = symbols.map((s) => {
  const allAliases = new Set(finalLabelsByApply.get(s.apply) ?? []);
  allAliases.delete(s.label);

  const extras = {};

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
  VERBOSE,
  C,
  col,
  hint,
  fmtLabels,
  groupByApply,
  pairs,
  commonPrefixLen,
});

runTests({
  base,
  symbols,
  enriched,
  report,
  leanAll,
  leanApplyToLabels,
  baseApplyToLabel,
  overrides,
  MERGE,
  fmtLabels,
  col,
  C,
  fromLean,
});
