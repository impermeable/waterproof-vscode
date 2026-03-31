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
 *
 * Update Lean table:
 *   bash symbols.sh
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
    fraktur:        false,  // fraktur A-Z a-z (g p q ...)
    doubleStruck:   false,  // blackboard bold A-Z (A B C ...)
    boldItalic:     false,  // bold/italic math letters
    misc:           false,  // everything else
};

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

// -- Step 1: load base symbols
const base = JSON.parse(fs.readFileSync(BASE, "utf8"));
const symbols = [...base];
const seenLabels = new Set(base.map(s => s.label));

// -- Step 2: add new characters from Lean table
const lean = JSON.parse(fs.readFileSync(LEAN, "utf8"));

for (const [key, value] of Object.entries(lean)) {
    const apply = Array.isArray(value) ? value[0] : value;

    // Skip bracket-pair templates, escapes, and multi-character symbols
    if (!apply || apply.includes("$CURSOR")) continue;
    if (apply === "\\" || apply === "\\n") continue;

    const label = key.startsWith("\\") ? key : "\\" + key;
    if (seenLabels.has(label)) continue;                    // skip duplicate labels
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
    // Omit symbolPanelCategory entirely when hidden
    const entry = cat !== undefined
        ? { label, type: "symbol", apply, symbolPanelCategory: cat }
        : { label, type: "symbol", apply };
    symbols.push(entry);
}

// -- Write output
fs.writeFileSync(OUTPUT, JSON.stringify(symbols, null, 4), "utf8");

const hidden  = symbols.filter(s => s.symbolPanelCategory === undefined).length;
const fromLean = symbols.length - base.length;
console.log(`Base symbols   : ${base.length}`);
console.log(`Added from Lean: ${fromLean}`);
console.log(`Total written  : ${symbols.length} (${symbols.length - hidden} in panel, ${hidden} hidden) -> ${OUTPUT}`);

// --- Tests ---
if (!TEST) process.exit(0);

console.log(`\nRunning tests against base file...`);
const outMap = new Map(symbols.map(s => [s.label, s]));
let pass = true;

function fail(msg) {
    pass = false;
    console.log("Failed: " + msg);
}

// 1. Base categories preserved
const catMismatches = base.filter(ref => {
    const out = outMap.get(ref.label);
    return out && out.symbolPanelCategory !== ref.symbolPanelCategory;
});
if (catMismatches.length > 0) {
    fail(`\nCategory mismatches (${catMismatches.length}):`);
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
    fail(`\nMissing labels (${missing.length}):`);
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
    fail(`\nApply mismatches (${applyMismatches.length}):`);
    for (const m of applyMismatches) {
        const got = outMap.get(m.label).apply;
        console.log(`   ${m.label.padEnd(25)} expected=${m.apply}  got=${got}`);
    }
} else {
    console.log(`✓ All base apply values preserved`);
}

// 4. No duplicate labels
const labelCounts = new Map();
for (const s of symbols) labelCounts.set(s.label, (labelCounts.get(s.label) ?? 0) + 1);
const dupLabels = [...labelCounts.entries()].filter(([, n]) => n > 1);
if (dupLabels.length > 0) {
    fail(`\nDuplicate labels (${dupLabels.length}):`);
    for (const [label, count] of dupLabels) console.log(`   ${label.padEnd(25)} (${count}x)`);
} else {
    console.log(`✓ No duplicate labels`);
}

// 5. Valid category values on Lean-added symbols (undefined = hidden)
const validCats = new Set([0, 1, 2, 3, 4, 5, 6, 7]);
const badCat = symbols.slice(base.length).filter(s => s.symbolPanelCategory !== undefined && !validCats.has(s.symbolPanelCategory));
if (badCat.length > 0) {
    fail(`\nInvalid category values in Lean-added symbols (${badCat.length}):`);
    for (const s of badCat) console.log(`   ${s.label.padEnd(25)} cat=${s.symbolPanelCategory}`);
} else {
    console.log(`✓ All Lean-added category values valid`);
}
// 6. No stray "type" fields on Lean-added symbols other than "symbol"
const hasType = symbols.slice(base.length).filter(s => s.type !== 'symbol');
if (hasType.length > 0) {
    fail(`\nLean-added symbols with unexpected "type" field (${hasType.length}):`);
    for (const s of hasType) console.log(`   ${s.label.padEnd(25)} type=${s.type}`);
} else {
    console.log(`✓ No stray "type" fields on Lean-added symbols`);
}

// 7. No multi-character apply values in Lean-added symbols
// const multiChar = symbols.slice(base.length).filter(s => [...s.apply].length > 1);
// if (multiChar.length > 0) {
//     fail(`\nMulti-character apply values in Lean-added symbols (${multiChar.length}):`);
//     for (const s of multiChar) console.log(`   ${s.label.padEnd(25)} apply=${s.apply}`);
// } else {
//     console.log(`✓ No multi-character apply values`);
// }

// 8. Overrides all resolved (catches typos in override labels)
const unresolvedOverrides = Object.keys(overrides).filter(label => !outMap.has(label));
if (unresolvedOverrides.length > 0) {
    fail(`\nOverride labels not found in output (${unresolvedOverrides.length}):`);
    for (const label of unresolvedOverrides) console.log(`   ${label}`);
} else if (Object.keys(overrides).length > 0) {
    console.log(`✓ All overrides resolved`);
}

// 9. Override categories applied correctly
const overrideMismatches = Object.entries(overrides).filter(([label, expectedCat]) => {
    const out = outMap.get(label);
    return out && out.symbolPanelCategory !== expectedCat;
});
if (overrideMismatches.length > 0) {
    fail(`\nOverride category mismatches (${overrideMismatches.length}):`);
    for (const [label, expectedCat] of overrideMismatches) {
        const got = outMap.get(label)?.symbolPanelCategory;
        console.log(`   ${label.padEnd(25)} expected=${expectedCat}  got=${got}`);
    }
} else if (Object.keys(overrides).length > 0) {
    console.log(`✓ All override categories applied correctly`);
}

// 10. Base symbol order preserved
const baseLabels = base.map(s => s.label);
const outLabels  = symbols.slice(0, base.length).map(s => s.label);
if (JSON.stringify(baseLabels) !== JSON.stringify(outLabels)) {
    fail(`\nBase symbol order not preserved`);
} else {
    console.log(`✓ Base symbol order preserved`);
}
const leanRaw = Object.entries(lean)
    .map(([key, value]) => ({ label: key.startsWith("\\") ? key : "\\" + key, apply: Array.isArray(value) ? value[0] : value }))
    .filter(({ apply }) => apply && !apply.includes("$CURSOR") && apply !== "\\" && apply !== "\\n" && [...apply].length === 1);

// 11. Informational: Lean symbols whose character already exists in symbols.json
const baseApplyMap = new Map(base.map(s => [s.apply, s.label]));
const leanByApply = new Map();
for (const { label, apply } of leanRaw) {
    if (!leanByApply.has(apply)) leanByApply.set(apply, []);
    leanByApply.get(apply).push(label);
}

const sharedChars = [...baseApplyMap.entries()]
    .filter(([apply]) => leanByApply.has(apply))
    .map(([apply, baseLabel]) => ({ apply, baseLabel, leanLabels: leanByApply.get(apply) }));

if (sharedChars.length > 0) {
    console.log(`\nℹ️  Characters in both symbols.json and Lean (${sharedChars.length}):`);
    console.log(`   ${"char".padEnd(5)} ${"U+".padEnd(8)} ${"waterproof label".padEnd(28)} lean labels`);
    console.log(`   ${"─".repeat(80)}`);
    for (const { apply, baseLabel, leanLabels } of sharedChars) {
        const cp = `U+${apply.codePointAt(0).toString(16).toUpperCase().padStart(4, "0")}`;
        console.log(`   ${apply.padEnd(5)} ${cp.padEnd(8)} ${baseLabel.padEnd(28)} ${leanLabels.join(", ")}`);
    }
}
// 12. Informational: Lean labels skipped because the label already exists in symbols.json
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

// 13. Informational: symbols.json entries not present in Lean at all
const leanLabels  = new Set(leanRaw.map(s => s.label));
const leanApplies = new Set(leanRaw.map(s => s.apply));
const baseOnlyLabel  = base.filter(s => !leanLabels.has(s.label));
const baseOnlyApply  = base.filter(s => !leanApplies.has(s.apply));
const baseOnlyBoth   = base.filter(s => !leanLabels.has(s.label) && !leanApplies.has(s.apply));
const baseOnlyLabelOnly  = baseOnlyLabel.filter(s => leanApplies.has(s.apply));
const baseOnlyApplyOnly  = baseOnlyApply.filter(s => leanLabels.has(s.label));

if (baseOnlyBoth.length > 0) {
    console.log(`\nℹ️  symbols.json entries absent from Lean entirely: label and character (${baseOnlyBoth.length}):`);
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
for (const s of symbols.slice(base.length, base.length + 20)) {
    console.log(`   ${s.label.padEnd(10)} ${s.apply}  cat=${s.symbolPanelCategory ?? "hidden"}`);
}
if (fromLean > 20) console.log(`   ... and ${fromLean - 20} more`);

console.log(`\n${pass ? "Test passed" : "Test FAILED"}`);
process.exit(pass ? 0 : 1);
