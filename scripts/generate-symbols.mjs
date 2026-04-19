/**
 * generate-symbols.mjs
 *
 * Merges the hand-curated symbols.json (BASE) with the Lean unicode table,
 * adding any characters from Lean that are not already in the base.
 *
 * Alias resolution strategy (approach 2):
 *   - All symbols from symbols.json are kept as-is (no deduplication).
 *   - From the Lean table, a character (`apply`) is only included if it does
 *     NOT already appear in symbols.json.
 *   - Among all Lean aliases for the same character, only the longest label
 *     is kept.
 *
 * Boosts:
 *   - All labels from symbols.json get BASE_BOOST added to their boost.
 *   - Among those, labels with a visible symbolPanelCategory (not undefined /
 *     null / 99) get an additional PANEL_BOOST.
 *
 * Console reports:
 *   1. Lean labels whose `apply` already exists in symbols.json AND whose label
 *      differs from the symbols.json label (the "already covered" removals).
 *   2. Lean labels removed because a longer alias for the same character exists
 *      (the "too short" removals), grouped by the winning label.
 *   3. Duplicate apply values within symbols.json itself (kept, but annotated
 *      with "Also: ..." detail and boosted).
 *
 * Categories:
 *   0  Greek lowercase      1  Greek uppercase
 *   2  Math / logic         3  Arrows
 *   4  Letterlike (N R ...)  5  Super / subscripts
 *   6  Calligraphic         7  Misc
 *   99 Hidden (completion-only, not shown in panel)
 *
 * Usage:
 *   node generate-symbols.mjs           # merge and write
 *   node generate-symbols.mjs --test    # merge, write, then run tests
 */

import fs from "fs";
import { fileURLToPath } from "url";
import path from "path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const BASE   = path.resolve(__dirname, "../completions/symbols.json");
const LEAN   = path.resolve(__dirname, "../node_modules/@leanprover/unicode-input/dist/abbreviations.json");
const OUTPUT = path.resolve(__dirname, "../completions/symbols+lean.json");
const TEST   = process.argv.includes("--test");

// CONFIGURATION
// Which groups of new symbols (from Lean) to show in the panel vs hide.
// Set a group to `true` to assign its natural category (visible in panel).
// Set to `false` to assign category 99 (completion-only, hidden from panel).
// This only affects symbols added from Lean. The base symbols.json is
// always preserved exactly as-is.
const SHOW_IN_PANEL = {
    greekLower:     false,   // α β γ ...
    greekUpper:     false,   // Α Β Γ ...
    mathLogic:      false,   // ∀ ∃ ∈ ...
    arrows:         false,   // → ← ⇒ ...
    letterlike:     false,   // N Z R C ...
    scripts:        false,   // superscripts, subscripts
    calligraphic:   false,   // script A-Z (A-Z ...)
    fraktur:        false,   // fraktur A-Z a-z (g p q ...)
    doubleStruck:   false,   // blackboard bold A-Z (A B C ...)
    boldItalic:     false,   // bold/italic math letters
    misc:           false,   // everything else
};

/**
 * Boost applied to all symbols.json entries so they sort above competing
 * Lean-only aliases for the same character.
 */
const BASE_BOOST = 5;

/**
 * Additional boost for symbols.json entries that have a visible panel category
 * (i.e. symbolPanelCategory is defined, non-null, and not 99).
 */
const PANEL_BOOST = 3;

// -- Unicode block -> category
// Each entry: [codepoint range, natural category, SHOW_IN_PANEL key]
const BLOCKS = [
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
    // Mathematical Alphanumeric block (U+1D400-1D7FF) -- split by sub-range:
    [[0x1D504, 0x1D56B], 6, "fraktur"],       // Fraktur + Bold Fraktur A-Z a-z
    [[0x1D538, 0x1D56B], 4, "doubleStruck"],  // Double-Struck (blackboard bold)
    [[0x1D400, 0x1D7FF], 6, "boldItalic"],    // everything else (bold, italic, sans, mono)
];

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

// -- Per-label overrides --
let overrides = {
    // Example: "foo": 3,  // assign category 3 (arrows) to symbol with label "foo"
};

// ---------------------------------------------------------------------------
// Step 1: load base symbols
// ---------------------------------------------------------------------------
const base = JSON.parse(fs.readFileSync(BASE, "utf8"));

// Set of apply characters already covered by symbols.json
const baseApplySet = new Set(base.map(s => s.apply));
// Map apply -> [label, ...] for all symbols.json entries (for report #3)
const baseApplyToLabels = new Map();
for (const s of base) {
    if (!baseApplyToLabels.has(s.apply)) baseApplyToLabels.set(s.apply, []);
    baseApplyToLabels.get(s.apply).push(s.label);
}

// ---------------------------------------------------------------------------
// Step 2: load Lean table and parse into a flat list of {label, apply} pairs
// ---------------------------------------------------------------------------
const lean = JSON.parse(fs.readFileSync(LEAN, "utf8"));

const leanRaw = Object.entries(lean)
    .map(([key, value]) => ({
        label: key.startsWith("\\") ? key : "\\" + key,
        apply: Array.isArray(value) ? value[0] : value,
    }))
    .filter(({ apply }) =>
        apply &&
        !apply.includes("$CURSOR") &&
        apply !== "\\" &&
        apply !== "\\n" &&
        [...apply].length === 1
    );

// ---------------------------------------------------------------------------
// Step 3: Split Lean entries into "already covered by base" vs "candidates"
// ---------------------------------------------------------------------------

// Lean entries whose apply is already in symbols.json — these are never added.
// For the report we only care about ones whose label DIFFERS from the base label.
const leanCoveredByBase = leanRaw.filter(({ apply }) => baseApplySet.has(apply));

// The differing ones are interesting for report #1
const leanCoveredDifferentLabel = leanCoveredByBase.filter(({ label, apply }) => {
    const baseLabels = baseApplyToLabels.get(apply) ?? [];
    return !baseLabels.includes(label);
});

// Candidates: Lean entries whose apply is NOT in symbols.json
const leanCandidates = leanRaw.filter(({ apply }) => !baseApplySet.has(apply));

// ---------------------------------------------------------------------------
// Step 4: Among candidates, keep only the longest label per apply character.
// When multiple labels tie for longest, pick the lexicographically largest
// (arbitrary but deterministic). Track only strictly-shorter labels as losers.
// ---------------------------------------------------------------------------

// apply -> all labels (needed for both winner selection and loser tracking)
const allLabelsByApply = new Map();
for (const { label, apply } of leanCandidates) {
    if (!allLabelsByApply.has(apply)) allLabelsByApply.set(apply, []);
    allLabelsByApply.get(apply).push(label);
}

// apply -> winning label (longest; ties broken lexicographically)
const longestByApply = new Map();
for (const [apply, labels] of allLabelsByApply) {
    const maxLen = Math.max(...labels.map(l => l.length));
    const winner = labels
        .filter(l => l.length === maxLen)
        .sort()
        .at(-1); // lexicographically largest among the tied-longest
    longestByApply.set(apply, winner);
}

// Removals because strictly shorter: winner label -> [removed labels]
// Labels that tie for longest with the winner are NOT considered losers.
const removedTooShort = new Map(); // winnerLabel -> removedLabels[]
for (const [apply, labels] of allLabelsByApply) {
    const winner = longestByApply.get(apply);
    const losers = labels.filter(l => l.length < winner.length);
    if (losers.length > 0) {
        removedTooShort.set(winner, losers);
    }
}

// ---------------------------------------------------------------------------
// Step 5: Build the final symbol list
// ---------------------------------------------------------------------------

const symbols = [...base];
const seenLabels = new Set(base.map(s => s.label));

for (const [apply, winnerLabel] of longestByApply) {
    if (seenLabels.has(winnerLabel)) continue; // shouldn't happen, but guard

    const cp = apply.codePointAt(0);

    let cat;
    if (overrides[winnerLabel] !== undefined) {
        cat = overrides[winnerLabel];
    } else if (/^\\[\^_]/.test(winnerLabel)) {
        cat = SHOW_IN_PANEL.scripts ? 5 : undefined;
    } else {
        const [naturalCat, groupKey] = categoryFromBlock(cp);
        cat = SHOW_IN_PANEL[groupKey] ? naturalCat : undefined;
    }

    seenLabels.add(winnerLabel);
    const entry = cat !== undefined
        ? { label: winnerLabel, type: "symbol", apply, symbolPanelCategory: cat }
        : { label: winnerLabel, type: "symbol", apply };
    symbols.push(entry);
}

// ---------------------------------------------------------------------------
// Step 6: Annotate base symbols with "Also: ..." detail for duplicate apply
//         values within symbols.json, and apply boosts.
// ---------------------------------------------------------------------------

// Build a map from label -> symbol entry (mutable copies)
const outMap = new Map(symbols.map(s => [s.label, { ...s }]));

// Re-link symbols array entries to the mutable copies
for (let i = 0; i < symbols.length; i++) {
    symbols[i] = outMap.get(symbols[i].label);
}

// Annotate base entries that share their apply with other base entries.
for (const [apply, labels] of baseApplyToLabels) {
    if (labels.length <= 1) continue;
    const sorted = [...labels].sort();
    for (const label of sorted) {
        const entry = outMap.get(label);
        if (!entry) continue;
        const others = sorted.filter(l => l !== label);
        entry.detail = "Also: " + others.join(", ");
    }
}

// Apply boosts to all base entries.
for (const s of base) {
    const entry = outMap.get(s.label);
    if (!entry) continue;
    entry.boost = (entry.boost ?? 0) + BASE_BOOST;
    // Additional boost for visible panel categories
    const cat = s.symbolPanelCategory;
    if (cat !== undefined && cat !== null && cat !== 99) {
        entry.boost += PANEL_BOOST;
    }
}

// ---------------------------------------------------------------------------
// Step 7: Write output
// ---------------------------------------------------------------------------
const output = symbols;
fs.writeFileSync(OUTPUT, JSON.stringify(output, null, 4), "utf8");

const fromLean = output.length - base.length;
const hidden   = output.filter(s => s.symbolPanelCategory === undefined).length;
console.log(`Base symbols   : ${base.length}`);
console.log(`Added from Lean: ${fromLean}`);
console.log(`Total written  : ${output.length} (${output.length - hidden} in panel, ${hidden} hidden) -> ${OUTPUT}`);

// Reverse map: winner label -> apply (for report 2 lookups)
const winnerToApply = new Map(
    [...longestByApply.entries()].map(([apply, winner]) => [winner, apply])
);

// Shared column widths for reports 1 and 2
const COL_SYM   = 5;
const COL_CP    = 8;
const COL_KEPT  = 32;
const REPORT_HEADER = `   ${"sym".padEnd(COL_SYM)} ${"U+".padEnd(COL_CP)} ${"kept".padEnd(COL_KEPT)} removed`;
const REPORT_SEP    = `   ${"=".repeat(COL_SYM + 1 + COL_CP + 1 + COL_KEPT + 1 + 20)}`;

// ---------------------------------------------------------------------------
// Report 1: Lean labels removed because their apply is already in symbols.json,
//           and the label itself differs from the base label(s).
//           All lean labels for the same apply appear on one line.
//           Format: sym | U+   | kept (base labels) | removed (lean labels)
// ---------------------------------------------------------------------------
if (leanCoveredDifferentLabel.length > 0) {
    // Group by apply so all removed lean labels for one character share a row
    const byApply = new Map();
    for (const { label, apply } of leanCoveredDifferentLabel) {
        if (!byApply.has(apply)) byApply.set(apply, []);
        byApply.get(apply).push(label);
    }
    console.log(`\nInfo  Lean aliases removed: character already in symbols.json (${leanCoveredDifferentLabel.length}):`);
    console.log(REPORT_HEADER);
    console.log(REPORT_SEP);
    for (const [apply, removedLabels] of [...byApply.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
        const cp      = `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
        const kept    = (baseApplyToLabels.get(apply) ?? []).sort().join(", ");
        const removed = removedLabels.sort().join(", ");
        console.log(`   ${apply.padEnd(COL_SYM)} ${cp.padEnd(COL_CP)} ${kept.padEnd(COL_KEPT)} ${removed}`);
    }
}

// ---------------------------------------------------------------------------
// Report 2: Lean labels removed because a longer alias for the same character
//           exists. All aliases for the same apply appear on one line.
//           Format: sym | U+   | kept (longest label) | removed (shorter labels)
// ---------------------------------------------------------------------------
if (removedTooShort.size > 0) {
    const totalRemoved = [...removedTooShort.values()].reduce((n, arr) => n + arr.length, 0);
    console.log(`\nInfo  Lean aliases removed: shorter alias for same character (${totalRemoved} removed, kept longest):`);
    console.log(REPORT_HEADER);
    console.log(REPORT_SEP);
    for (const [winner, losers] of [...removedTooShort.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
        const apply   = winnerToApply.get(winner) ?? "?";
        const cp      = apply !== "?" ? `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}` : "?";
        const removed = losers.sort().join(", ");
        console.log(`   ${apply.padEnd(COL_SYM)} ${cp.padEnd(COL_CP)} ${winner.padEnd(COL_KEPT)} ${removed}`);
    }
}

// ---------------------------------------------------------------------------
// Report 3: Duplicate apply values within symbols.json itself.
// ---------------------------------------------------------------------------
const baseDuplicates = [...baseApplyToLabels.entries()].filter(([, labels]) => labels.length > 1);
if (baseDuplicates.length > 0) {
    console.log(`\nℹ️  Duplicate apply values in symbols.json (kept, not deduplicated) (${baseDuplicates.length} characters):`);
    console.log(`   ${"char".padEnd(5)} ${"U+".padEnd(8)} labels`);
    console.log(`   ${"─".repeat(60)}`);
    for (const [apply, labels] of baseDuplicates.sort((a, b) => a[0].localeCompare(b[0]))) {
        const cp = `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
        const annotated = labels.map(l => {
            const isAlsoListed = outMap.get(l)?.detail ? " [has detail]" : "";
            return l + isAlsoListed;
        }).join(", ");
        console.log(`   ${apply.padEnd(5)} ${cp.padEnd(8)} ${annotated}`);
    }
}

// Legacy informational: Lean labels skipped because the label already exists in symbols.json
//    Split into: same apply (true alias) vs different apply (conflict)
const skippedSameApply = [];
const skippedDiffApply = [];
for (const { label, apply } of leanRaw) {
    if (!seenLabels.has(label)) continue; // was added, not skipped
    const baseEntry = outMap.get(label);
    if (!baseEntry) continue; // shouldn't happen
    if (baseEntry.apply === apply) {
        skippedSameApply.push({ label, apply });
    } else {
        skippedDiffApply.push({ label, leanApply: apply, baseApply: baseEntry.apply });
    }
}

if (skippedDiffApply.length > 0) {
    console.log(`\nℹ️  Lean labels skipped: label exists in symbols.json but with different character (${skippedDiffApply.length}):`);
    for (const s of skippedDiffApply) {
        console.log(`   ${s.label.padEnd(25)} base: ${s.baseApply}  lean: ${s.leanApply}`);
    }
} else {
    console.log(`✓ No Lean labels conflict with symbols.json`);
}

// Legacy informational: symbols.json entries not present in Lean at all
const leanLabels  = new Set(leanRaw.map(s => s.label));
const leanApplies = new Set(leanRaw.map(s => s.apply));
const baseOnlyBoth   = base.filter(s => !leanLabels.has(s.label) && !leanApplies.has(s.apply));
const baseOnlyLabelOnly  = base.filter(s => !leanLabels.has(s.label) && leanApplies.has(s.apply));
const baseOnlyApplyOnly  = base.filter(s => leanLabels.has(s.label) && !leanApplies.has(s.apply));

if (baseOnlyBoth.length > 0) {
    console.log(`\nℹ️  symbols.json entries absent from Lean entirely (${baseOnlyBoth.length}):`);
    for (const s of baseOnlyBoth) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
}
if (baseOnlyLabelOnly.length > 0) {
    console.log(`\nℹ️  symbols.json entries whose label is not in Lean (but character is) (${baseOnlyLabelOnly.length}):`);
    for (const s of baseOnlyLabelOnly) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
}
if (baseOnlyApplyOnly.length > 0) {
    console.log(`\nℹ️  symbols.json entries whose character is not in Lean (but label is) (${baseOnlyApplyOnly.length}):`);
    for (const s of baseOnlyApplyOnly) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
}
if (baseOnlyBoth.length === 0 && baseOnlyLabelOnly.length === 0 && baseOnlyApplyOnly.length === 0) {
    console.log(`✓ All symbols.json entries have both label and character present in Lean`);
}

console.log(`\n${fromLean} new symbols added from Lean table (first 20):`);
for (const s of output.slice(base.length, base.length + 20)) {
    console.log(`   ${s.label.padEnd(10)} ${s.apply}  cat=${s.symbolPanelCategory ?? "hidden"}${s.detail ? "  detail=" + s.detail : ""}`);
}
if (fromLean > 20) console.log(`   ... and ${fromLean - 20} more`);

// =============================================================================
// Tests
// =============================================================================
if (!TEST) process.exit(0);

console.log(`\n${"─".repeat(70)}`);
console.log(`Running tests...`);
let pass = true;

function fail(msg) {
    pass = false;
    console.log("FAILED: " + msg);
}

function ok(msg) {
    console.log("✓ " + msg);
}

// 1. Base categories preserved
const catMismatches = base.filter(ref => {
    const out = outMap.get(ref.label);
    return out && out.symbolPanelCategory !== ref.symbolPanelCategory;
});
if (catMismatches.length > 0) {
    fail(`Category mismatches (${catMismatches.length}):`);
    for (const m of catMismatches) {
        const got = outMap.get(m.label).symbolPanelCategory;
        console.log(`   ${m.label.padEnd(25)} ${m.apply}  expected=${m.symbolPanelCategory}  got=${got}`);
    }
} else {
    console.log(`✓ All base categories preserved`);
}

// 2. Base labels preserved
const missing = base.filter(r => !outMap.has(r.label));
if (missing.length > 0) {
    fail(`Missing labels (${missing.length}):`);
    for (const m of missing) console.log(`   ${m.label.padEnd(25)} ${m.apply}`);
} else {
    console.log(`✓ All base labels preserved`);
}

// 3. Base apply values preserved
const applyMismatches = base.filter(ref => {
    const out = outMap.get(ref.label);
    return out && out.apply !== ref.apply;
});
if (applyMismatches.length > 0) {
    fail(`Apply mismatches (${applyMismatches.length}):`);
    for (const m of applyMismatches) {
        const got = outMap.get(m.label).apply;
        console.log(`   ${m.label.padEnd(25)} expected=${m.apply}  got=${got}`);
    }
} else {
    console.log(`✓ All base apply values preserved`);
}

// 4. No duplicate labels
const labelCounts = new Map();
for (const s of output) labelCounts.set(s.label, (labelCounts.get(s.label) ?? 0) + 1);
const dupLabels = [...labelCounts.entries()].filter(([, n]) => n > 1);
if (dupLabels.length > 0) {
    fail(`Duplicate labels (${dupLabels.length}):`);
    for (const [label, count] of dupLabels) console.log(`   ${label.padEnd(25)} (${count}x)`);
} else {
    console.log(`✓ No duplicate labels`);
}

// 5. Valid category values on Lean-added symbols (undefined = hidden)
const validCats = new Set([0, 1, 2, 3, 4, 5, 6, 7]);
const badCat = output.slice(base.length).filter(s => s.symbolPanelCategory !== undefined && !validCats.has(s.symbolPanelCategory));
if (badCat.length > 0) {
    fail(`Invalid category values in Lean-added symbols (${badCat.length}):`);
    for (const s of badCat) console.log(`   ${s.label.padEnd(25)} cat=${s.symbolPanelCategory}`);
} else {
    console.log(`✓ All Lean-added category values valid`);
}

// 6. No stray "type" fields on Lean-added symbols other than "symbol"
const hasType = output.slice(base.length).filter(s => s.type !== 'symbol');
if (hasType.length > 0) {
    fail(`Lean-added symbols with unexpected "type" field (${hasType.length}):`);
    for (const s of hasType) console.log(`   ${s.label.padEnd(25)} type=${s.type}`);
} else {
    console.log(`✓ No stray "type" fields on Lean-added symbols`);
}

// 7. Overrides all resolved (catches typos in override labels)
const unresolvedOverrides = Object.keys(overrides).filter(label => !outMap.has(label));
if (unresolvedOverrides.length > 0) {
    fail(`Override labels not found in output (${unresolvedOverrides.length}):`);
    for (const label of unresolvedOverrides) console.log(`   ${label}`);
} else if (Object.keys(overrides).length > 0) {
    console.log(`✓ All overrides resolved`);
}

// 8. Override categories applied correctly
const overrideMismatches = Object.entries(overrides).filter(([label, expectedCat]) => {
    const out = outMap.get(label);
    return out && out.symbolPanelCategory !== expectedCat;
});
if (overrideMismatches.length > 0) {
    fail(`Override category mismatches (${overrideMismatches.length}):`);
    for (const [label, expectedCat] of overrideMismatches) {
        const got = outMap.get(label)?.symbolPanelCategory;
        console.log(`   ${label.padEnd(25)} expected=${expectedCat}  got=${got}`);
    }
} else if (Object.keys(overrides).length > 0) {
    console.log(`✓ All override categories applied correctly`);
}

// 9. Base symbol order preserved
const baseLabels = base.map(s => s.label);
const outLabels  = output.slice(0, base.length).map(s => s.label);
if (JSON.stringify(baseLabels) !== JSON.stringify(outLabels)) {
    fail(`Base symbol order not preserved`);
} else {
    console.log(`✓ Base symbol order preserved`);
}

// ---------------------------------------------------------------------------
// NEW TESTS — approach 2 invariants
// ---------------------------------------------------------------------------

// T-N1: No Lean-added symbol has an apply that is already in symbols.json
const leanAdded = output.slice(base.length);
const leanAddedWithBaseApply = leanAdded.filter(s => baseApplySet.has(s.apply));
if (leanAddedWithBaseApply.length > 0) {
    fail(`Lean-added symbols whose apply is already in symbols.json (${leanAddedWithBaseApply.length}):`);
    for (const s of leanAddedWithBaseApply)
        console.log(`   ${s.label.padEnd(25)} apply=${s.apply}`);
} else {
    ok("No Lean-added symbol has an apply already covered by symbols.json");
}

// T-N2: For every Lean-added symbol, no other Lean alias for the same apply is strictly longer
const leanAddedByApply = new Map(leanAdded.map(s => [s.apply, s.label]));
let longestWins = true;
for (const [apply, winnerLabel] of leanAddedByApply) {
    // All Lean raw candidates for this apply (excluding base-covered)
    const allForApply = leanCandidates.filter(e => e.apply === apply).map(e => e.label);
    const maxLen = Math.max(...allForApply.map(l => l.length));
    if (winnerLabel.length < maxLen) {
        fail(`Lean-added label for '${apply}' is not the longest: kept=${winnerLabel} (len=${winnerLabel.length}), max len=${maxLen}`);
        longestWins = false;
    }
}
if (longestWins) ok("For every Lean-added character, the longest alias was kept");

// T-N3: All base entries have boost >= BASE_BOOST
const baseWithLowBoost = base.filter(s => {
    const entry = outMap.get(s.label);
    return !entry || (entry.boost ?? 0) < BASE_BOOST;
});
if (baseWithLowBoost.length > 0) {
    fail(`Base entries with boost < ${BASE_BOOST} (${baseWithLowBoost.length}):`);
    for (const s of baseWithLowBoost)
        console.log(`   ${s.label.padEnd(25)} boost=${outMap.get(s.label)?.boost ?? "missing"}`);
} else {
    ok(`All base entries have boost >= ${BASE_BOOST}`);
}

// T-N4: Base entries with visible symbolPanelCategory have boost >= BASE_BOOST + PANEL_BOOST
const baseVisibleWithLowBoost = base.filter(s => {
    const cat = s.symbolPanelCategory;
    if (cat === undefined || cat === null || cat === 99) return false;
    const entry = outMap.get(s.label);
    return !entry || (entry.boost ?? 0) < BASE_BOOST + PANEL_BOOST;
});
if (baseVisibleWithLowBoost.length > 0) {
    fail(`Base entries with visible category but boost < ${BASE_BOOST + PANEL_BOOST} (${baseVisibleWithLowBoost.length}):`);
    for (const s of baseVisibleWithLowBoost)
        console.log(`   ${s.label.padEnd(25)} cat=${s.symbolPanelCategory}  boost=${outMap.get(s.label)?.boost ?? "missing"}`);
} else {
    ok(`All base entries with visible category have boost >= ${BASE_BOOST + PANEL_BOOST}`);
}

// T-N5: Lean-added symbols have no boost (they are not from base)
const leanWithBoost = leanAdded.filter(s => s.boost !== undefined);
if (leanWithBoost.length > 0) {
    fail(`Lean-added symbols unexpectedly have a boost field (${leanWithBoost.length}):`);
    for (const s of leanWithBoost)
        console.log(`   ${s.label.padEnd(25)} boost=${s.boost}`);
} else {
    ok("Lean-added symbols have no boost field");
}

// T-N6: detail fields only exist on base entries that share their apply with another base entry
const leanWithDetail = leanAdded.filter(s => s.detail !== undefined);
if (leanWithDetail.length > 0) {
    fail(`Lean-added symbols unexpectedly have a detail field (${leanWithDetail.length}):`);
    for (const s of leanWithDetail)
        console.log(`   ${s.label.padEnd(25)} detail=${s.detail}`);
} else {
    ok("Only base entries carry detail fields");
}

// T-N7: detail field symmetry — if A lists B in detail, B must list A
let detailSym = true;
for (const s of output) {
    if (!s.detail) continue;
    if (!s.detail.startsWith("Also: ")) {
        fail(`detail field for ${s.label} does not start with "Also: ": ${s.detail}`);
        detailSym = false;
        continue;
    }
    const listed = s.detail.slice("Also: ".length).split(", ");
    for (const lbl of listed) {
        const peer = outMap.get(lbl);
        if (!peer) {
            fail(`detail of ${s.label} references non-existent label ${lbl}`);
            detailSym = false;
        } else if (peer.apply !== s.apply) {
            fail(`detail of ${s.label} references ${lbl} which has a different apply char`);
            detailSym = false;
        } else if (!peer.detail || !peer.detail.slice("Also: ".length).split(", ").includes(s.label)) {
            fail(`detail asymmetry: ${s.label} lists ${lbl}, but ${lbl} does not list ${s.label}`);
            detailSym = false;
        }
    }
    if (listed.includes(s.label)) {
        fail(`detail of ${s.label} references itself`);
        detailSym = false;
    }
}
if (detailSym) ok("All detail fields are well-formed and symmetric");

// T-N8: leanCoveredDifferentLabel only includes labels whose apply is in baseApplySet
//        and whose label is NOT among the base labels for that apply
const badCovered = leanCoveredDifferentLabel.filter(({ label, apply }) => {
    if (!baseApplySet.has(apply)) return true;
    const baseLabelsForApply = baseApplyToLabels.get(apply) ?? [];
    return baseLabelsForApply.includes(label); // should NOT be in here
});
if (badCovered.length > 0) {
    fail(`leanCoveredDifferentLabel contains entries that are the same as base label (${badCovered.length}):`);
    for (const { label, apply } of badCovered)
        console.log(`   ${label.padEnd(25)} apply=${apply}`);
} else {
    ok("Report 1 (leanCoveredDifferentLabel) contains only genuinely different labels");
}

// T-N9: Every loser in removedTooShort is strictly shorter than the winner
//        (ties in length are kept as additional winners, not removed)
let tooShortOk = true;
for (const [winner, losers] of removedTooShort) {
    for (const loser of losers) {
        if (loser.length >= winner.length) {
            fail(`"Too short" removal: ${loser} (len=${loser.length}) is not strictly shorter than winner ${winner} (len=${winner.length})`);
            tooShortOk = false;
        }
    }
}
if (tooShortOk) ok("All 'too short' removals: every removed alias is strictly shorter than the winner");

// T-N10: No Lean-added symbol's label is a key in the base label set
const leanLabelCollidesWithBase = leanAdded.filter(s => base.some(b => b.label === s.label));
if (leanLabelCollidesWithBase.length > 0) {
    fail(`Lean-added symbols collide on label with a base symbol (${leanLabelCollidesWithBase.length}):`);
    for (const s of leanLabelCollidesWithBase)
        console.log(`   ${s.label}`);
} else {
    ok("No Lean-added label collides with a base label");
}

console.log(`\n${pass ? "✅ All tests passed" : "❌ Some tests FAILED"}`);
process.exit(pass ? 0 : 1);
