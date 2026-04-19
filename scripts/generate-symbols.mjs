/**
 * generate-symbols.mjs
 *
 * Merges the hand-curated symbols.json (BASE) with the Lean unicode table,
 * adding any characters from Lean that are not already in the base.
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
 *   node generate-symbols.mjs --test    # merge, write, then compare against base
 */

import fs from "fs";
import { fileURLToPath } from "url";
import path from "path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const BASE   = path.resolve(__dirname, "../completions/symbols.json");
const LEAN   = path.resolve(__dirname, "../node_modules/@leanprover/unicode-input/dist/abbreviations.json");
const OUTPUT = path.resolve(__dirname, "../completions/symbols+lean.json");
const TEST   = process.argv.includes("--test");

const ANSI = {
    reset: "\x1b[0m",
    cyan: "\x1b[36m",
    green: "\x1b[32m",
};
const USE_COLOR = process.stdout.isTTY;

function paint(text, color) {
    return USE_COLOR ? `${color}${text}${ANSI.reset}` : text;
}

function originTag(isBase) {
    return isBase
        ? paint("[base]", ANSI.green)
        : paint("[lean]", ANSI.cyan);
}

function codePointLabel(ch) {
    if (!ch) return "n/a";
    return `U+${ch.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
}

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
 * Boost applied to base (symbols.json) entries so they sort higher in
 * completion lists when competing with Lean-only aliases for the same text.
 */
const BASE_BOOST = 5;

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
// Alias-deduplication helpers
// ---------------------------------------------------------------------------

/**
 * Returns true when `shorter` is a strict prefix of `longer` (both strings,
 * same start, shorter.length < longer.length).
 */
function isStrictPrefix(shorter, longer) {
    return shorter.length < longer.length && longer.startsWith(shorter);
}

/**
 * Given a set of labels that all resolve to the same `apply` character,
 * decide which labels survive and which are eliminated.
 *
 * Rules (applied per connected prefix-cluster):
 *  1. Within any group where every label is an exact prefix of another label
 *     in that group, keep only the longest — UNLESS one or more of them come
 *     from symbols.json (isBase), in which case keep ALL base labels and
 *     remove only non-base labels that are prefixes of a base label (or of a
 *     longer label in the group regardless of origin).
 *  2. Labels that are not in any prefix relationship with any other label in
 *     the same apply-group are always kept.
 *
 * Returns { survivors: Set<string>, eliminated: Map<string, string> }
 * where eliminated maps a removed label → the label that "won".
 */
function resolveAliases(labels, baseSet) {
    // Build prefix relationships: a → b means a is a strict prefix of b.
    // We only care about pairs within this label set.
    const labelArr = [...labels];

    // eliminated[label] = winner label
    const eliminated = new Map();
    const survivors  = new Set(labelArr);

    // For each pair, if one is a strict prefix of the other, the shorter
    // one may be eliminated.
    for (let i = 0; i < labelArr.length; i++) {
        for (let j = 0; j < labelArr.length; j++) {
            if (i === j) continue;
            const shorter = labelArr[i];
            const longer  = labelArr[j];
            if (!isStrictPrefix(shorter, longer)) continue;

            // `shorter` is a prefix of `longer`.
            // Eliminate `shorter` unless it is in the base set.
            if (!baseSet.has(shorter)) {
                // Non-base shorter is eliminated in favour of longer.
                if (survivors.has(shorter)) {
                    eliminated.set(shorter, longer);
                    survivors.delete(shorter);
                }
            }
            // If shorter IS in the base, we keep it and instead eliminate
            // `longer` if longer is not in the base.
            else if (!baseSet.has(longer)) {
                if (survivors.has(longer)) {
                    eliminated.set(longer, shorter);
                    survivors.delete(longer);
                }
            }
            // Both are in base → keep both (do nothing).
        }
    }

    return { survivors, eliminated };
}

/**
 * Count the number of leading characters (after the leading backslash) that
 * two labels share. The backslash itself is excluded from the count.
 */
function sharedPrefixLength(a, b) {
    // Strip leading backslash for the comparison
    const ca = a.startsWith("\\") ? a.slice(1) : a;
    const cb = b.startsWith("\\") ? b.slice(1) : b;
    let n = 0;
    while (n < ca.length && n < cb.length && ca[n] === cb[n]) n++;
    return n;
}

// ---------------------------------------------------------------------------
// Step 1: load base symbols
// ---------------------------------------------------------------------------
const base = JSON.parse(fs.readFileSync(BASE, "utf8"));
const baseSet = new Set(base.map(s => s.label));

// We'll build the final list in two phases:
// Phase A – collect all candidates (base + lean)
// Phase B – apply alias resolution, inject details, write output

// Map from label → raw entry (pre-detail-injection)
const allEntries = new Map(); // label → {label, type, apply, symbolPanelCategory?, boost?}

// Populate with base entries first (they carry their existing categories)
for (const s of base) {
    allEntries.set(s.label, { ...s, _isBase: true });
}

// ---------------------------------------------------------------------------
// Step 2: load Lean table and add new entries
// ---------------------------------------------------------------------------
const lean = JSON.parse(fs.readFileSync(LEAN, "utf8"));
const seenLabels = new Set(base.map(s => s.label));

for (const [key, value] of Object.entries(lean)) {
    const apply = Array.isArray(value) ? value[0] : value;

    // Skip bracket-pair templates, escapes, and multi-character symbols
    if (!apply || apply.includes("$CURSOR")) continue;
    if (apply === "\\" || apply === "\\n") continue;

    const label = key.startsWith("\\") ? key : "\\" + key;
    if (seenLabels.has(label)) continue; // skip duplicate labels
    // Note: duplicate apply values are allowed (multiple labels -> same character)

    const cp = apply.codePointAt(0);

    let cat;
    if (overrides[label] !== undefined) {
        cat = overrides[label];
    } else if (/^\\[\^_]/.test(label)) {
        cat = SHOW_IN_PANEL.scripts ? 5 : undefined;
    } else {
        const [naturalCat, groupKey] = categoryFromBlock(cp);
        cat = SHOW_IN_PANEL[groupKey] ? naturalCat : undefined;
    }

    seenLabels.add(label);
    const entry = cat !== undefined
        ? { label, type: "symbol", apply, symbolPanelCategory: cat, _isBase: false }
        : { label, type: "symbol", apply, _isBase: false };
    allEntries.set(label, entry);
}

// ---------------------------------------------------------------------------
// Step 3: group labels by apply character, then resolve aliases
// ---------------------------------------------------------------------------

// applyToLabels: apply char → Set of labels
const applyToLabels = new Map();
for (const [label, entry] of allEntries) {
    const { apply } = entry;
    if (!applyToLabels.has(apply)) applyToLabels.set(apply, new Set());
    applyToLabels.get(apply).add(label);
}

// Global tracking for reporting
const allEliminated   = new Map(); // label → winner label
const allSurvivorSets = new Map(); // apply → Set<label> (after resolution)

// Non-prefix alias groups for informational reporting
// apply → [ {label, isBase} ]
const nonPrefixAliasGroups = new Map();

for (const [apply, labels] of applyToLabels) {
    if (labels.size === 1) {
        allSurvivorSets.set(apply, labels);
        continue;
    }

    const { survivors, eliminated } = resolveAliases(labels, baseSet);
    for (const [elim, winner] of eliminated) allEliminated.set(elim, winner);
    allSurvivorSets.set(apply, survivors);

    // Collect non-prefix alias pairs for info reporting
    const survivorArr = [...survivors];
    if (survivorArr.length > 1) {
        // Find pairs that are NOT in a prefix relationship
        const nonPrefixPairs = [];
        for (let i = 0; i < survivorArr.length; i++) {
            for (let j = i + 1; j < survivorArr.length; j++) {
                const a = survivorArr[i], b = survivorArr[j];
                if (!isStrictPrefix(a, b) && !isStrictPrefix(b, a)) {
                    nonPrefixPairs.push([a, b]);
                }
            }
        }
        if (nonPrefixPairs.length > 0) {
            nonPrefixAliasGroups.set(apply, survivorArr.map(l => ({
                label: l,
                isBase: baseSet.has(l)
            })));
        }
    }
}

const labelToApply = new Map([...allEntries.entries()].map(([label, entry]) => [label, entry.apply]));

// Remove eliminated entries
for (const label of allEliminated.keys()) {
    allEntries.delete(label);
}

// ---------------------------------------------------------------------------
// Step 4: inject "Also: ..." detail and boost base entries
// ---------------------------------------------------------------------------
for (const [apply, survivors] of allSurvivorSets) {
    if (survivors.size <= 1) {
        // Single survivor — still apply boost if base
        if (survivors.size === 1) {
            const [lbl] = survivors;
            const entry = allEntries.get(lbl);
            if (entry && entry._isBase) {
                entry.boost = (entry.boost ?? 0) + BASE_BOOST;
            }
        }
        continue;
    }

    const survivorArr = [...survivors].sort();
    for (const label of survivorArr) {
        const entry = allEntries.get(label);
        if (!entry) continue;

        const others = survivorArr.filter(l => l !== label);
        if (others.length > 0) {
            entry.detail = "Also: " + others.join(", ");
        }

        if (entry._isBase) {
            entry.boost = (entry.boost ?? 0) + BASE_BOOST;
        }
    }
}

// ---------------------------------------------------------------------------
// Step 5: build final ordered array
// ---------------------------------------------------------------------------
// Base symbols first (preserve order), then Lean-added symbols.
const symbols = [];
const addedLabels = new Set();

for (const s of base) {
    if (allEntries.has(s.label)) {
        symbols.push(allEntries.get(s.label));
        addedLabels.add(s.label);
    }
}
for (const [label, entry] of allEntries) {
    if (!addedLabels.has(label)) {
        symbols.push(entry);
    }
}

// Strip internal _isBase flag before writing
const output = symbols.map(({ _isBase, ...rest }) => rest);
const outMap = new Map(output.map(s => [s.label, s]));

// ---------------------------------------------------------------------------
// Step 6: write output
// ---------------------------------------------------------------------------
fs.writeFileSync(OUTPUT, JSON.stringify(output, null, 4), "utf8");

const hidden   = output.filter(s => s.symbolPanelCategory === undefined).length;
console.log("\nMerge summary");
console.log(`  Base symbols    : ${base.length}`);
console.log(`  Added from Lean : ${output.length - base.length} (after alias removal)`);
console.log(`  Total written   : ${output.length} (${output.length - hidden} in panel, ${hidden} hidden)`);
console.log(`  Output file     : ${OUTPUT}`);

// ---------------------------------------------------------------------------
// Informational: alias elimination report
// ---------------------------------------------------------------------------
if (allEliminated.size > 0) {
    console.log(`\n📋 Alias elimination report (${allEliminated.size} labels removed):`);
    console.log(`   ${"sym".padEnd(4)} ${"U+".padEnd(8)} ${"eliminated label".padEnd(30)} ${"winner label".padEnd(30)} ${"elim".padEnd(8)} winner`);
    console.log(`   ${"-".repeat(101)}`);
    for (const [elim, winner] of [...allEliminated.entries()].sort()) {
        const apply = labelToApply.get(elim) ?? labelToApply.get(winner);
        const cp = codePointLabel(apply);
        const elimOrigin = originTag(baseSet.has(elim));
        const winnerOrigin = originTag(baseSet.has(winner));
        console.log(`   ${(apply ?? "?").padEnd(4)} ${cp.padEnd(8)} ${elim.padEnd(30)} ${winner.padEnd(30)} ${elimOrigin.padEnd(8)} ${winnerOrigin}`);
    }
}

// ---------------------------------------------------------------------------
// Informational: non-prefix aliases grouped by shared-prefix length
// ---------------------------------------------------------------------------
if (nonPrefixAliasGroups.size > 0) {
    // Collect all (a, b, sharedLen, applyChar) tuples
    const npTuples = [];
    for (const [apply, labelInfos] of nonPrefixAliasGroups) {
        const arr = labelInfos.map(x => x.label);
        for (let i = 0; i < arr.length; i++) {
            for (let j = i + 1; j < arr.length; j++) {
                const a = arr[i], b = arr[j];
                if (!isStrictPrefix(a, b) && !isStrictPrefix(b, a)) {
                    npTuples.push({
                        apply,
                        a, b,
                        aBase: baseSet.has(a),
                        bBase: baseSet.has(b),
                        shared: sharedPrefixLength(a, b)
                    });
                }
            }
        }
    }
    // Sort by descending shared prefix length (most similar first)
    npTuples.sort((x, y) => y.shared - x.shared || x.a.localeCompare(y.a));

    // Group by shared length, then by apply-character for compact display
    // sharedLen -> applyChar -> { labels: Set<string>, pairs: number }
    const byShared = new Map();
    for (const t of npTuples) {
        if (!byShared.has(t.shared)) byShared.set(t.shared, new Map());
        const applyGroups = byShared.get(t.shared);
        if (!applyGroups.has(t.apply)) {
            applyGroups.set(t.apply, { labels: new Set(), pairs: 0 });
        }
        const bucket = applyGroups.get(t.apply);
        bucket.labels.add(t.a);
        bucket.labels.add(t.b);
        bucket.pairs += 1;
    }

    const sharedGroups = [...byShared.entries()]
        .sort((a, b) => b[0] - a[0])
        .filter(([shared]) => shared > 0);

    if (sharedGroups.length > 0) {
        console.log(`\n🔀 Non-prefix alias pairs, ranked by shared leading letters (excluding \\):`);
    }
    for (const [shared, applyGroups] of sharedGroups) {
        const totalPairs = [...applyGroups.values()].reduce((sum, g) => sum + g.pairs, 0);
        const pairWord = totalPairs === 1 ? "pair" : "pairs";
        const symbolWord = applyGroups.size === 1 ? "symbol" : "symbols";
        console.log(`\n  Shared ${shared} letter(s): ${totalPairs} ${pairWord}, ${applyGroups.size} ${symbolWord}`);

        const sortedByApply = [...applyGroups.entries()].sort((a, b) => {
            const aliasDiff = b[1].labels.size - a[1].labels.size;
            if (aliasDiff !== 0) return aliasDiff;
            return a[0].localeCompare(b[0]);
        });
        for (const [apply, group] of sortedByApply) {
            const labels = [...group.labels].sort();
            const rendered = labels.map(label => `${label} ${originTag(baseSet.has(label))}`).join(", ");
            console.log(`    '${apply}' ${codePointLabel(apply).padEnd(8)} | ${rendered}`);
        }
    }
}

// ---------------------------------------------------------------------------
// Informational: legacy reports
// ---------------------------------------------------------------------------

const leanRaw = Object.entries(lean)
    .map(([key, value]) => ({ label: key.startsWith("\\") ? key : "\\" + key, apply: Array.isArray(value) ? value[0] : value }))
    .filter(({ apply }) => apply && !apply.includes("$CURSOR") && apply !== "\\" && apply !== "\\n" && [...apply].length === 1);

// Shared characters between symbols.json and Lean
const baseApplyMap = new Map(base.map(s => [s.apply, s.label]));
const leanByApply  = new Map();
for (const { label, apply } of leanRaw) {
    if (!leanByApply.has(apply)) leanByApply.set(apply, []);
    leanByApply.get(apply).push(label);
}

const sharedChars = [...baseApplyMap.entries()]
    .filter(([apply]) => leanByApply.has(apply))
    .map(([apply, baseLabel]) => ({ apply, baseLabel, leanLabels: leanByApply.get(apply) }));

if (sharedChars.length > 0) {
    console.log(`\nℹ️  Characters in both symbols.json and Lean (${sharedChars.length}):`);
    console.log(`   ${"char".padEnd(5)} ${"U+".padEnd(8)} ${"base label".padEnd(28)} lean labels`);
    console.log(`   ${"─".repeat(80)}`);
    for (const { apply, baseLabel, leanLabels } of sharedChars) {
        const cp = `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
        console.log(`   ${apply.padEnd(5)} ${cp.padEnd(8)} ${baseLabel.padEnd(28)} ${leanLabels.join(", ")}`);
    }
}

// Lean labels with conflicting apply
const skippedDiffApply = [];
for (const { label, apply } of leanRaw) {
    const baseEntry = outMap.get(label);
    if (!baseEntry) continue;
    if (baseEntry.apply !== apply) {
        skippedDiffApply.push({ label, leanApply: apply, baseApply: baseEntry.apply });
    }
}
if (skippedDiffApply.length > 0) {
    console.log(`\nℹ️  Lean labels whose label exists in symbols.json but with different character (${skippedDiffApply.length}):`);
    for (const s of skippedDiffApply) {
        console.log(`   ${s.label.padEnd(25)} base: ${s.baseApply}  lean: ${s.leanApply}`);
    }
} else {
    console.log("✓ No Lean labels conflict with symbols.json");
}

// symbols.json entries absent from Lean
const leanLabels   = new Set(leanRaw.map(s => s.label));
const leanApplies  = new Set(leanRaw.map(s => s.apply));
const baseOnlyBoth = base.filter(s => !leanLabels.has(s.label) && !leanApplies.has(s.apply));
const baseOnlyLabelOnly = base.filter(s => !leanLabels.has(s.label) && leanApplies.has(s.apply));
const baseOnlyApplyOnly = base.filter(s => leanLabels.has(s.label) && !leanApplies.has(s.apply));

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
    console.log("✓ All symbols.json entries have both label and character present in Lean");
}

console.log(`\n${output.length - base.length} new symbols added from Lean table (first 20):`);
for (const s of output.slice(base.length, base.length + 20)) {
    console.log(`   ${s.label.padEnd(12)} ${s.apply}  cat=${s.symbolPanelCategory ?? "hidden"}${s.detail ? "  detail=" + s.detail : ""}`);
}
if (output.length - base.length > 20) console.log(`   ... and ${output.length - base.length - 20} more`);

// =============================================================================
// Tests
// =============================================================================
if (!TEST) process.exit(0);

console.log(`\n${"─".repeat(70)}`);
console.log(`Running tests against base file...`);
let pass = true;

function fail(msg) {
    pass = false;
    console.log("FAILED: " + msg);
}

function ok(msg) {
    console.log("✓ " + msg);
}

// ---------------------------------------------------------------------------
// Original tests (adapted)
// ---------------------------------------------------------------------------

// 1. Base categories preserved
const catMismatches = base.filter(ref => {
    if (!outMap.has(ref.label)) return false; // will be caught by test 2
    const out = outMap.get(ref.label);
    return out.symbolPanelCategory !== ref.symbolPanelCategory;
});
if (catMismatches.length > 0) {
    fail(`Category mismatches (${catMismatches.length}):`);
    for (const m of catMismatches) {
        const got = outMap.get(m.label).symbolPanelCategory;
        console.log(`   ${m.label.padEnd(25)} ${m.apply}  expected=${m.symbolPanelCategory}  got=${got}`);
    }
} else {
    ok("All base categories preserved");
}

// 2. Base labels preserved (unless legitimately eliminated — base labels should NEVER be eliminated)
const missingBase = base.filter(r => !outMap.has(r.label));
if (missingBase.length > 0) {
    fail(`Base labels missing from output (${missingBase.length}) — base labels must never be eliminated:`);
    for (const m of missingBase) console.log(`   ${m.label.padEnd(25)} ${m.apply}`);
} else {
    ok("All base labels preserved");
}

// 3. Base apply values preserved
const applyMismatches = base.filter(ref => {
    if (!outMap.has(ref.label)) return false;
    return outMap.get(ref.label).apply !== ref.apply;
});
if (applyMismatches.length > 0) {
    fail(`Apply mismatches (${applyMismatches.length}):`);
    for (const m of applyMismatches) {
        const got = outMap.get(m.label).apply;
        console.log(`   ${m.label.padEnd(25)} expected=${m.apply}  got=${got}`);
    }
} else {
    ok("All base apply values preserved");
}

// 4. No duplicate labels
const labelCounts = new Map();
for (const s of output) labelCounts.set(s.label, (labelCounts.get(s.label) ?? 0) + 1);
const dupLabels = [...labelCounts.entries()].filter(([, n]) => n > 1);
if (dupLabels.length > 0) {
    fail(`Duplicate labels (${dupLabels.length}):`);
    for (const [label, count] of dupLabels) console.log(`   ${label.padEnd(25)} (${count}x)`);
} else {
    ok("No duplicate labels");
}

// 5. Valid category values on Lean-added symbols (undefined = hidden)
const validCats = new Set([0, 1, 2, 3, 4, 5, 6, 7]);
const baseLabelsInOutput = new Set(base.map(s => s.label).filter(l => outMap.has(l)));
const leanAdded = output.filter(s => !baseLabelsInOutput.has(s.label));
const badCat = leanAdded.filter(s => s.symbolPanelCategory !== undefined && !validCats.has(s.symbolPanelCategory));
if (badCat.length > 0) {
    fail(`Invalid category values in Lean-added symbols (${badCat.length}):`);
    for (const s of badCat) console.log(`   ${s.label.padEnd(25)} cat=${s.symbolPanelCategory}`);
} else {
    ok("All Lean-added category values valid");
}

// 6. No stray "type" fields on Lean-added symbols other than "symbol"
const hasType = leanAdded.filter(s => s.type !== "symbol");
if (hasType.length > 0) {
    fail(`Lean-added symbols with unexpected "type" field (${hasType.length}):`);
    for (const s of hasType) console.log(`   ${s.label.padEnd(25)} type=${s.type}`);
} else {
    ok("No stray \"type\" fields on Lean-added symbols");
}

// 7. Overrides all resolved
const unresolvedOverrides = Object.keys(overrides).filter(label => !outMap.has(label));
if (unresolvedOverrides.length > 0) {
    fail(`Override labels not found in output (${unresolvedOverrides.length}):`);
    for (const label of unresolvedOverrides) console.log(`   ${label}`);
} else if (Object.keys(overrides).length > 0) {
    ok("All overrides resolved");
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
    ok("All override categories applied correctly");
}

// 9. Base symbol order preserved
const baseLabelsOrdered = base.map(s => s.label).filter(l => outMap.has(l));
const outFirstN = output.slice(0, baseLabelsOrdered.length).map(s => s.label);
if (JSON.stringify(baseLabelsOrdered) !== JSON.stringify(outFirstN)) {
    fail("Base symbol order not preserved");
} else {
    ok("Base symbol order preserved");
}

// ---------------------------------------------------------------------------
// NEW TESTS: Alias deduplication
// ---------------------------------------------------------------------------

// T-A1: Base labels are NEVER eliminated
const baseEliminated = [...allEliminated.keys()].filter(l => baseSet.has(l));
if (baseEliminated.length > 0) {
    fail(`Base labels were eliminated (must never happen) (${baseEliminated.length}):`);
    for (const l of baseEliminated) console.log(`   ${l}  →  ${allEliminated.get(l)}`);
} else {
    ok("No base labels were eliminated");
}

// T-A2: Every eliminated label is a strict prefix of its winner
const badElim = [...allEliminated.entries()].filter(([elim, winner]) =>
    !isStrictPrefix(elim, winner) && !isStrictPrefix(winner, elim)
);
if (badElim.length > 0) {
    fail(`Eliminated labels not in prefix relationship with winner (${badElim.length}):`);
    for (const [elim, winner] of badElim)
        console.log(`   ${elim.padEnd(30)} →  ${winner}`);
} else {
    ok("All eliminated labels are strict prefixes of their winner");
}

// T-A3: No two surviving labels for the same apply-char are in a prefix relationship
//       (unless both are base, in which case it's intentional)
let prefixSurvivorBug = false;
for (const [apply, survivors] of allSurvivorSets) {
    const arr = [...survivors];
    for (let i = 0; i < arr.length; i++) {
        for (let j = 0; j < arr.length; j++) {
            if (i === j) continue;
            if (isStrictPrefix(arr[i], arr[j])) {
                // Allowed only if both are in base
                if (!(baseSet.has(arr[i]) && baseSet.has(arr[j]))) {
                    if (!prefixSurvivorBug) {
                        fail("Surviving labels in prefix relationship (non-base):");
                        prefixSurvivorBug = true;
                    }
                    const tag = l => baseSet.has(l) ? "[base]" : "[lean]";
                    console.log(`   '${apply}': ${arr[i]} ${tag(arr[i])} is prefix of ${arr[j]} ${tag(arr[j])}`);
                }
            }
        }
    }
}
if (!prefixSurvivorBug) ok("No unwanted prefix-relationship survivors");

// T-A4: detail field format check — must start with "Also: " when present,
//        and list only labels that also survive and share the same apply char.
let detailOk = true;
for (const s of output) {
    if (!s.detail) continue;
    if (!s.detail.startsWith("Also: ")) {
        fail(`detail field for ${s.label} does not start with "Also: ": ${s.detail}`);
        detailOk = false;
        continue;
    }
    const listed = s.detail.slice("Also: ".length).split(", ");
    for (const lbl of listed) {
        const peer = outMap.get(lbl);
        if (!peer) {
            fail(`detail of ${s.label} references non-existent label ${lbl}`);
            detailOk = false;
        } else if (peer.apply !== s.apply) {
            fail(`detail of ${s.label} references ${lbl} which has different apply char`);
            detailOk = false;
        }
    }
    // Also check label does NOT reference itself
    if (listed.includes(s.label)) {
        fail(`detail of ${s.label} references itself`);
        detailOk = false;
    }
}
if (detailOk) ok("All detail fields are well-formed");

// T-A5: Symmetry of detail — if A lists B, B must list A
let detailSym = true;
for (const s of output) {
    if (!s.detail) continue;
    const listed = s.detail.slice("Also: ".length).split(", ");
    for (const lbl of listed) {
        const peer = outMap.get(lbl);
        if (!peer || !peer.detail) {
            fail(`detail asymmetry: ${s.label} lists ${lbl}, but ${lbl} has no detail`);
            detailSym = false;
            continue;
        }
        const peerListed = peer.detail.slice("Also: ".length).split(", ");
        if (!peerListed.includes(s.label)) {
            fail(`detail asymmetry: ${s.label} lists ${lbl}, but ${lbl} doesn't list ${s.label}`);
            detailSym = false;
        }
    }
}
if (detailSym) ok("detail fields are symmetric (if A lists B, B lists A)");

// T-A6: Base entries with aliases get a boost >= BASE_BOOST
let boostOk = true;
for (const s of output) {
    if (!baseSet.has(s.label)) continue;
    // Check if this apply char has multiple survivors
    const survivors = allSurvivorSets.get(s.apply);
    if (survivors && survivors.size > 1) {
        if (!s.boost || s.boost < BASE_BOOST) {
            fail(`Base entry ${s.label} should have boost >= ${BASE_BOOST}, got ${s.boost}`);
            boostOk = false;
        }
    }
}
if (boostOk) ok(`Base entries with aliases have boost >= ${BASE_BOOST}`);

// T-A7: resolveAliases unit tests (pure logic, no file I/O)
{
    let unitPass = true;
    const check = (desc, got, expected) => {
        const gs = JSON.stringify([...got].sort());
        const es = JSON.stringify([...expected].sort());
        if (gs !== es) {
            fail(`resolveAliases unit [${desc}]: expected survivors ${es}, got ${gs}`);
            unitPass = false;
        }
    };

    // Case 1: all lean, one is prefix → longest wins
    {
        const { survivors } = resolveAliases(new Set(["\\le", "\\leq", "\\leqq"]), new Set());
        check("all-lean prefix chain", survivors, ["\\leqq"]);
    }

    // Case 2: base is shorter, lean is longer → lean eliminated (base protected, lean prefix of base is dropped)
    {
        const { survivors } = resolveAliases(new Set(["\\le", "\\leq"]), new Set(["\\le"]));
        check("base shorter, lean longer → lean eliminated", survivors, ["\\le"]);
    }


    // Case 3: base is longer, lean is shorter → lean eliminated
    {
        const { survivors } = resolveAliases(new Set(["\\le", "\\leq"]), new Set(["\\leq"]));
        check("base longer, lean shorter → lean eliminated", survivors, ["\\leq"]);
    }

    // Case 4: two base labels both survive regardless of prefix
    {
        const { survivors } = resolveAliases(new Set(["\\le", "\\leq"]), new Set(["\\le", "\\leq"]));
        check("both base → both survive", survivors, ["\\le", "\\leq"]);
    }

    // Case 5: no prefix relationship → all survive
    {
        const { survivors } = resolveAliases(new Set(["\\leq", "\\lte"]), new Set());
        check("no prefix relation → both survive", survivors, ["\\leq", "\\lte"]);
    }

    // Case 6: three-way chain, all lean → only longest survives
    {
        const { survivors } = resolveAliases(new Set(["\\a", "\\ab", "\\abc"]), new Set());
        check("three-way chain all lean → longest only", survivors, ["\\abc"]);
    }

    // Case 7: base in middle of chain → shorter lean eliminated,
    //          longer lean ALSO eliminated (base trumps it as the longer survives
    //          only if base is the shorter; here base is \\ab and \\abc is lean,
    //          so \\ab is prefix of \\abc and \\ab is base → \\abc eliminated)
    {
        const { survivors } = resolveAliases(new Set(["\\a", "\\ab", "\\abc"]), new Set(["\\ab"]));
        check("base in middle → all non-base labels eliminated", survivors, ["\\ab"]);
    }
  

    if (unitPass) ok("resolveAliases unit tests all pass");
}

// T-A8: Every apply character has at least one surviving label
let applyLostBug = false;
for (const [apply, survivors] of allSurvivorSets) {
    if (survivors.size === 0) {
        if (!applyLostBug) {
            fail("Some apply characters have no surviving labels (symbol lost entirely):");
            applyLostBug = true;
        }
        const cp = `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
        console.log(`   '${apply}' (${cp}) — all labels eliminated`);
    }
}
if (!applyLostBug) ok("Every apply character has at least one surviving label");

console.log(`\n${pass ? "✅ All tests passed" : "❌ Some tests FAILED"}`);
process.exit(pass ? 0 : 1);
