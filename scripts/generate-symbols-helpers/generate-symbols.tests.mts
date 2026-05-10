import type { BaseSymbol, SymbolEntry, TestContext } from "./generate-symbols.types.mjs";

export function runTests(ctx: TestContext): void {
    const {
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
        fromLean: fromLeanInput,
    } = ctx;

    const ICONS = {
        info: "\u2139\uFE0F",
        ok:   "\u2713",
        fail: "\u2717",
    };

    const fromLean = fromLeanInput ?? (symbols.length - base.length);

    const leanRaw        = [...leanAll.entries()].map(([label, apply]) => ({ label, apply }));
    const leanLabelsSet  = new Set(leanRaw.map(s => s.label));
    const leanAppliesSet = new Set(leanRaw.map(s => s.apply));

    // Informational: Characters in both symbols.json AND Lean
    const sharedChars = [...baseApplyToLabel.entries()]
        .filter(([apply]) => leanApplyToLabels.has(apply))
        .map(([apply, baseLabel]) => ({
            apply,
            baseLabel,
            leanLabels: [...leanApplyToLabels.get(apply)!],
        }));

    if (sharedChars.length > 0) {
        console.log(`\n${col(C.cyan, `${ICONS.info}  Characters in both symbols.json and Lean (${sharedChars.length}):`)}`);
        console.log(`   ${"char".padEnd(5)} ${"U+".padEnd(8)} ${"base label".padEnd(28)} lean labels`);
        console.log(`   ${"\u2500".repeat(80)}`);
        for (const { apply, baseLabel, leanLabels } of sharedChars) {
            const cp = `U+${apply.codePointAt(0)!.toString(16).toUpperCase().padStart(4, "0")}`;
            console.log(`   ${apply.padEnd(5)} ${cp.padEnd(8)} ${baseLabel.padEnd(28)} ${fmtLabels(leanLabels)}`);
        }
    }

    // symbols.json entries absent from Lean
    const baseOnlyBoth      = base.filter(s => !leanLabelsSet.has(s.label) && !leanAppliesSet.has(s.apply));
    const baseOnlyLabelOnly = base.filter(s => !leanLabelsSet.has(s.label) &&  leanAppliesSet.has(s.apply));
    const baseOnlyApplyOnly = base.filter(s =>  leanLabelsSet.has(s.label) && !leanAppliesSet.has(s.apply));

    if (baseOnlyBoth.length > 0) {
        console.log(`\n${col(C.cyan, `${ICONS.info}  symbols.json entries absent from Lean entirely - label AND character (${baseOnlyBoth.length}):`)}`);
        for (const s of baseOnlyBoth) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
    }
    if (baseOnlyLabelOnly.length > 0) {
        console.log(`\n${col(C.cyan, `${ICONS.info}  symbols.json entries whose label is not in Lean, but character is (${baseOnlyLabelOnly.length}):`)}`);
        for (const s of baseOnlyLabelOnly) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
    }
    if (baseOnlyApplyOnly.length > 0) {
        console.log(`\n${col(C.cyan, `${ICONS.info}  symbols.json entries whose character is not in Lean, but label is (${baseOnlyApplyOnly.length}):`)}`);
        for (const s of baseOnlyApplyOnly) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
    }
    if (baseOnlyBoth.length === 0 && baseOnlyLabelOnly.length === 0 && baseOnlyApplyOnly.length === 0) {
        console.log(`${ICONS.ok}  All symbols.json entries have both label and character present in Lean`);
    }

    console.log(`\n${fromLean} new symbols added from Lean table (first 20):`);
    for (const s of symbols.slice(base.length, base.length + 20)) {
        console.log(`   ${s.label.padEnd(10)} ${s.apply}  cat=${s.symbolPanelCategory ?? "hidden"}`);
    }
    if (fromLean > 20) console.log(`   ... and ${fromLean - 20} more`);

    console.log(`\nRunning tests against base file...`);

    const outMap = new Map<string, SymbolEntry>(symbols.map(s => [s.label, s]));
    let pass = true;

    function fail(msg: string): void {
        pass = false;
        console.log(col(C.red, "FAILED: ") + msg);
    }

    // 1. Base categories preserved
    const catMismatches = base.filter(ref => {
        const out = outMap.get(ref.label);
        return out && out.symbolPanelCategory !== ref.symbolPanelCategory;
    });
    if (catMismatches.length > 0) {
        fail(`Category mismatches (${catMismatches.length}):`);
        for (const m of catMismatches) {
            const got = outMap.get(m.label)!.symbolPanelCategory;
            console.log(`   ${m.label.padEnd(25)} ${m.apply}  expected=${m.symbolPanelCategory}  got=${got}`);
        }
    } else {
        console.log(`${ICONS.ok}  All base categories preserved`);
    }

    // 2. Base labels preserved
    const missing = base.filter(r => !outMap.has(r.label));
    if (missing.length > 0) {
        fail(`Missing labels (${missing.length}):`);
        for (const m of missing) console.log(`   ${m.label.padEnd(25)} ${m.apply}`);
    } else {
        console.log(`${ICONS.ok}  All base labels preserved`);
    }

    // 3. Base apply values preserved
    const applyMismatches = base.filter(ref => {
        const out = outMap.get(ref.label);
        return out && out.apply !== ref.apply;
    });
    if (applyMismatches.length > 0) {
        fail(`Apply mismatches (${applyMismatches.length}):`);
        for (const m of applyMismatches) {
            const got = outMap.get(m.label)!.apply;
            console.log(`   ${m.label.padEnd(25)} expected=${m.apply}  got=${got}`);
        }
    } else {
        console.log(`${ICONS.ok}  All base apply values preserved`);
    }

    // 4. No duplicate labels
    const labelCounts = new Map<string, number>();
    for (const s of symbols) labelCounts.set(s.label, (labelCounts.get(s.label) ?? 0) + 1);
    const dupLabels = [...labelCounts.entries()].filter(([, n]) => n > 1);
    if (dupLabels.length > 0) {
        fail(`Duplicate labels (${dupLabels.length}):`);
        for (const [label, count] of dupLabels) console.log(`   ${label.padEnd(25)} (${count}x)`);
    } else {
        console.log(`${ICONS.ok}  No duplicate labels`);
    }

    // 5. Valid category values on Lean-added symbols (undefined = hidden)
    const validCats = new Set([0, 1, 2, 3, 4, 5, 6, 7]);
    const badCat = symbols.slice(base.length).filter(
        s => s.symbolPanelCategory !== undefined && !validCats.has(s.symbolPanelCategory)
    );
    if (badCat.length > 0) {
        fail(`Invalid category values in Lean-added symbols (${badCat.length}):`);
        for (const s of badCat) console.log(`   ${s.label.padEnd(25)} cat=${s.symbolPanelCategory}`);
    } else {
        console.log(`${ICONS.ok}  All Lean-added category values valid`);
    }

    // 6. No stray "type" fields on Lean-added symbols other than "symbol"
    const hasType = symbols.slice(base.length).filter(s => s.type !== "symbol");
    if (hasType.length > 0) {
        fail(`Lean-added symbols with unexpected "type" field (${hasType.length}):`);
        for (const s of hasType) console.log(`   ${s.label.padEnd(25)} type=${s.type}`);
    } else {
        console.log(`${ICONS.ok}  No stray "type" fields on Lean-added symbols`);
    }

    // 7. Overrides all resolved (catches typos in override labels)
    const unresolvedOverrides = Object.keys(overrides).filter(label => !outMap.has(label));
    if (unresolvedOverrides.length > 0) {
        fail(`Override labels not found in output (${unresolvedOverrides.length}):`);
        for (const label of unresolvedOverrides) console.log(`   ${label}`);
    } else if (Object.keys(overrides).length > 0) {
        console.log(`${ICONS.ok}  All overrides resolved`);
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
        console.log(`${ICONS.ok}  All override categories applied correctly`);
    }

    // 9. Base symbol order preserved
    const baseLabels = base.map(s => s.label);
    const outLabels  = symbols.slice(0, base.length).map(s => s.label);
    if (JSON.stringify(baseLabels) !== JSON.stringify(outLabels)) {
        fail("Base symbol order not preserved");
    } else {
        console.log(`${ICONS.ok}  Base symbol order preserved`);
    }

    // 10. No lean-added symbols incorrectly reuse base applies
    if (!MERGE.addLatexIfAlreadyInBase) {
        const baseApplies  = new Set(base.map(s => s.apply));
        const invalidApply = symbols.slice(base.length).filter(s => baseApplies.has(s.apply));
        if (invalidApply.length > 0) {
            fail(`Lean-added symbols reuse a base apply (${invalidApply.length}):`);
            for (const s of invalidApply) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
        } else {
            console.log(`${ICONS.ok}  No lean-added symbols incorrectly reuse base applies`);
        }
    } else {
        // addLatexIfAlreadyInBase intentionally emits entries sharing a base apply,
        // so instead just verify those entries do not clobber an existing base label.
        const baseLabelSet = new Set(base.map(s => s.label));
        const clobbered    = symbols.slice(base.length).filter(s => baseLabelSet.has(s.label));
        if (clobbered.length > 0) {
            fail(`Lean-added symbols duplicate a base label (${clobbered.length}):`);
            for (const s of clobbered) console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
        } else {
            console.log(`${ICONS.ok}  No lean-added symbols duplicate a base label`);
        }
    }

    // 11. All latex-matching lean labels for the same apply are present in output
    let latexCoverFail = false;
    for (const r of report.addedViaLatex) {
        for (const lbl of r.addedLabels) {
            if (!outMap.has(lbl)) {
                if (!latexCoverFail) {
                    fail("Some latex-matched lean labels missing from output:");
                    latexCoverFail = true;
                }
                console.log(`   ${lbl.padEnd(28)} ${r.apply}`);
            }
        }
    }
    if (!latexCoverFail) console.log(`${ICONS.ok}  All latex-matched lean labels present in output`);

    // 12. Boost fields are within expected range when set
    const badBoost = enriched.filter(
        s => s.boost !== undefined && (typeof s.boost !== "number" || s.boost < 0)
    );
    if (badBoost.length > 0) {
        fail(`Symbols with invalid boost values (${badBoost.length}):`);
        for (const s of badBoost) console.log(`   ${s.label.padEnd(25)} boost=${s.boost}`);
    } else {
        console.log(`${ICONS.ok}  All boost values valid`);
    }

    console.log(`\n${pass ? col(C.green, `${ICONS.ok} Tests passed`) : col(C.red, `${ICONS.fail} Tests FAILED`)}`);
    process.exit(pass ? 0 : 1);
}