import type { ReportContext } from "./generate-symbols.types.mts";
import {
  C,
  col,
  hint,
  fmtLabels,
  fmtCp,
  groupByApply,
  pairs,
  commonPrefixLen,
} from "./generate-symbols.utils.mts";

export function runReports(ctx: ReportContext): void {
  const {
    multiCodepoint,
    report,
    symbols,
    latexApplyToLabels,
    latexLabelToApply,
    latexBraceLabels,
    leanLabelStrategy,
    VERBOSE,
    base,
    baseApplyToLabels,
    leanApplyToLabels,
  } = ctx;

  const ICONS = {
    warn: "⚠️",
    ok: "✅",
    info: "ℹ️",
  };

  // Map from final symbol -> apply
  const finalByApply = new Map<string, string[]>();
  for (const s of symbols) {
    if (!finalByApply.has(s.apply)) finalByApply.set(s.apply, []);
    finalByApply.get(s.apply)!.push(s.label);
  }

  // R1: Lean applies skipped - apply already in symbols.json
  if (report.skippedByApply.size > 0) {
    console.log(
      `\n${col(
        C.yellow,
        `${ICONS.warn}  Lean symbols skipped - apply already in symbols.json, extra lean aliases dropped. (${report.skippedByApply.size} characters) Symbols that do not appear in LaTeX get marked yellow:`,
      )}`,
    );
    for (const [
      apply,
      { baseLabels, droppedLabels, latexLabels },
    ] of report.skippedByApply) {
      const baseLabelsSet = new Set(baseLabels);
      const latexOthers = latexLabels.filter((l) => !baseLabelsSet.has(l));
      const coloredBaseLabels = baseLabels
        .map((l) => col(latexLabels.includes(l) ? C.cyan : C.yellow, l))
        .join(", ");
      const latexStr =
        latexOthers.length > 0
          ? `  ${col(C.gray, "latex:")} ${col(C.blue, fmtLabels(latexOthers))}`
          : "";
      console.log(
        `   ${col(C.bold, apply)}  ` +
          `${col(C.gray, "base:")} ${coloredBaseLabels}${latexStr}  ` +
          `${col(C.gray, "dropped:")} ${col(C.red, fmtLabels(droppedLabels))}`,
      );
    }
  }

  // R2a: New symbols added - latex alias chosen
  if (report.addedViaLatex.length > 0) {
    const totalEntries = report.addedViaLatex.reduce(
      (n, r) => n + r.addedLabels.length,
      0,
    );
    console.log(
      `\n${col(
        C.green,
        `${ICONS.ok}  New symbols added - latex alias chosen (${report.addedViaLatex.length} characters, ${totalEntries} entries):`,
      )}`,
    );
    for (const r of report.addedViaLatex) {
      const latexOthers = r.latexLabels.filter(
        (l) => !r.addedLabels.includes(l),
      );
      const latexStr =
        latexOthers.length > 0
          ? `  ${col(C.gray, "other latex:")} ${col(
              C.blue,
              fmtLabels(latexOthers),
            )}`
          : "";
      const dropStr =
        r.droppedLean.length > 0
          ? `  ${col(C.gray, "dropped:")} ${col(
              C.red,
              fmtLabels(r.droppedLean),
            )}`
          : "";
      console.log(
        `   ${col(C.bold, r.apply)}  ` +
          `${col(C.gray, "added:")} ${col(C.green, fmtLabels(r.addedLabels))}` +
          `${latexStr}${dropStr}`,
      );
    }
  }

  // R2b: New symbols added - lean fallback (no latex alias)
  {
    const totalLeanEntries = report.addedViaLean.reduce(
      (n, r) => n + r.addedLabels.length,
      0,
    );
    if (VERBOSE) {
      if (report.addedViaLean.length > 0) {
        console.log(
          `\n${col(
            C.magenta,
            `${ICONS.ok}  New symbols added - lean fallback, no latex alias (${report.addedViaLean.length} characters, ${totalLeanEntries} entries):`,
          )}`,
        );
        for (const r of report.addedViaLean) {
          console.log(
            `   ${col(C.bold, r.apply)}  ` +
              `${col(C.gray, "added:")} ${col(
                C.magenta,
                fmtLabels(r.addedLabels),
              )}`,
          );
        }
      }
    } else {
      console.log(
        `\n${col(
          C.magenta,
          `${ICONS.ok}  New symbols added - lean fallback, no latex alias:`,
        )} ` +
          `${col(
            C.bold,
            `${report.addedViaLean.length} characters, ${totalLeanEntries} entries`,
          )}  ` +
          hint("use --verbose to list them"),
      );
    }
  }

  // R2c: Lean fallback labels dropped by leanLabelStrategy
  {
    const totalDropped = report.filteredLean.reduce(
      (n, r) => n + r.droppedLabels.length,
      0,
    );
    if (leanLabelStrategy === "all") {
      // No filtering active - skip this section entirely
    } else if (report.filteredLean.length === 0) {
      console.log(
        `\n${col(
          C.cyan,
          `${ICONS.info}  Lean label strategy "${leanLabelStrategy}": no labels dropped`,
        )} ${col(
          C.gray,
          "(every lean-only character had at most one eligible label)",
        )}`,
      );
    } else {
      console.log(
        `\n${col(
          C.yellow,
          `${ICONS.warn}  Lean label strategy "${leanLabelStrategy}" - labels dropped from lean-only characters (${report.filteredLean.length} characters, ${totalDropped} labels dropped):`,
        )}`,
      );
      for (const r of report.filteredLean) {
        console.log(
          `   ${col(C.bold, r.apply)} ${col(C.gray, fmtCp(r.apply))}  ` +
            `${col(C.gray, "kept:")} ${col(
              C.green,
              fmtLabels(r.keptLabels),
            )}  ` +
            `${col(C.gray, "dropped:")} ${col(
              C.red,
              fmtLabels(r.droppedLabels),
            )}`,
        );
      }
    }
  }

  // R3: Label conflicts
  if (report.labelConflicts.length > 0) {
    console.log(
      `\n${col(
        C.red,
        `${ICONS.warn}  Lean labels conflicting with symbols.json - same label, different character (${report.labelConflicts.length}):`,
      )}`,
    );
    for (const lc of report.labelConflicts) {
      console.log(
        `   ${col(C.bold, lc.label.padEnd(28))}` +
          `  ${col(C.gray, "base:")} ${lc.baseApply}  ` +
          `${col(C.gray, "lean:")} ${lc.leanApply}`,
      );
    }
  }

  // R4: Final-symbol aliases vs latex-unicode aliases, paired per character
  console.log("\n" + "-".repeat(47));
  console.log("    Final symbol list vs LaTeX symbol list");
  console.log("-".repeat(47));

  const appliesInBoth = [...finalByApply.keys()].filter((a) =>
    latexApplyToLabels.has(a),
  );
  const finalOnlyItems: Array<{ apply: string; label: string }> = [];
  const latexOnlyItems: Array<{ apply: string; label: string }> = [];

  for (const apply of appliesInBoth) {
    const finalLabels = new Set(finalByApply.get(apply));
    const latexLabels = latexApplyToLabels.get(apply)!;
    for (const ll of latexLabels) {
      if (!finalLabels.has(ll)) latexOnlyItems.push({ apply, label: ll });
    }
    for (const fl of finalLabels) {
      if (!latexLabels.has(fl)) finalOnlyItems.push({ apply, label: fl });
    }
  }

  if (finalOnlyItems.length > 0 || latexOnlyItems.length > 0) {
    const differApplyItems = finalOnlyItems.filter(({ label }) =>
      latexLabelToApply.has(label),
    );
    const absentItems = finalOnlyItems.filter(
      ({ label }) => !latexLabelToApply.has(label),
    );
    const diffCmdItems = latexOnlyItems;

    // Group 1: same label resolves to a different character in LaTeX
    if (differApplyItems.length > 0) {
      const byApply = groupByApply(differApplyItems);
      console.log(
        `\n${col(
          C.cyan,
          `${ICONS.info}  Final label resolves to different character than in LaTeX (${byApply.size} chars, ${differApplyItems.length} labels):`,
        )}`,
      );
      for (const [apply, labels] of byApply) {
        const labelsWithLatexTarget = labels.map((label) => {
          const latexApply = latexLabelToApply.get(label);
          return `${label} ${col(C.gray, "LaTeX:")} ${col(
            C.yellow,
            latexApply ?? "?",
          )}`;
        });
        console.log(
          `   ${col(C.bold, apply)}  ` + labelsWithLatexTarget.join("  "),
        );
      }
    }

    // Group 2: LaTeX uses a different command for the same character
    if (diffCmdItems.length > 0) {
      const byApply = groupByApply(diffCmdItems);
      console.log(
        `\n${col(
          C.cyan,
          `${ICONS.info}  LaTeX uses a different command for same character in final output (${byApply.size} chars, ${diffCmdItems.length} labels):`,
        )}`,
      );
      for (const [apply, latexLabels] of byApply) {
        const finalLabels = finalByApply.get(apply) ?? [];
        const finalStr =
          finalLabels.length > 0
            ? `${col(C.gray, "final:")} ${fmtLabels(finalLabels)}  `
            : "";
        console.log(
          `   ${col(C.bold, apply)}  ` +
            `${finalStr}` +
            `${col(C.gray, "latex:")} ${col(C.blue, fmtLabels(latexLabels))}`,
        );
      }
    }

    // Group 3: final label does not appear in LaTeX at all
    {
      const byApply = groupByApply(absentItems);
      if (VERBOSE && absentItems.length > 0) {
        console.log(
          `\n${col(
            C.cyan,
            `${ICONS.info}  Final labels not in LaTeX at all (${byApply.size} chars, ${absentItems.length} labels):`,
          )}`,
        );
        for (const [apply, labels] of byApply) {
          console.log(`   ${col(C.bold, apply)}  ${fmtLabels(labels)}`);
        }
      } else if (absentItems.length > 0) {
        console.log(
          `\n${col(
            C.cyan,
            `${ICONS.info}  Final labels not in LaTeX at all:`,
          )} ` +
            `${col(
              C.bold,
              `${byApply.size} chars, ${absentItems.length} labels`,
            )}  ` +
            hint("use --verbose to list them"),
        );
      }
    }
  }

  // R5: LaTeX labels with {} (not usable as lean-style symbols)
  {
    const braceByApply = groupByApply(latexBraceLabels);
    if (VERBOSE) {
      if (latexBraceLabels.length > 0) {
        console.log(
          `\n${col(
            C.cyan,
            `${ICONS.info}  LaTeX labels containing {} - skipped as aliases (${latexBraceLabels.length}):`,
          )}`,
        );
        for (const [apply, labels] of braceByApply) {
          console.log(
            `   ${col(C.bold, apply)}  ${col(C.blue, fmtLabels(labels))}`,
          );
        }
      }
    } else if (latexBraceLabels.length > 0) {
      console.log(
        `\n${col(
          C.cyan,
          `${ICONS.info}  LaTeX labels containing {} - skipped as aliases:`,
        )} ` +
          `${col(
            C.bold,
            `${latexBraceLabels.length} entries across ${braceByApply.size} characters`,
          )}  ` +
          hint("use --verbose to list them"),
      );
    }
  }

  // R6: Matching-prefix alias pairs in the final symbol list
  const prefixReport: Array<{
    apply: string;
    labels: string[];
    maxCommon: number;
  }> = [];
  for (const [apply, labels] of finalByApply) {
    if (labels.length < 2) continue;
    let maxCommon = 0;
    const matchingPairs: Array<{ a: string; b: string; common: number }> = [];
    for (const [a, b] of pairs(labels)) {
      const common = commonPrefixLen(a, b);
      if (common > 0) {
        matchingPairs.push({ a, b, common });
        if (common > maxCommon) maxCommon = common;
      }
    }
    if (matchingPairs.length === 0) continue;
    const involvedLabels = [
      ...new Set(matchingPairs.flatMap((p) => [p.a, p.b])),
    ];
    prefixReport.push({ apply, labels: involvedLabels, maxCommon });
  }

  prefixReport.sort((a, b) => b.maxCommon - a.maxCommon);
  if (prefixReport.length > 0) {
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  Aliases with matching prefixes in final output - ranked by prefix length (${prefixReport.length} characters):`,
      )}`,
    );
    for (const { apply, labels, maxCommon } of prefixReport) {
      console.log(
        `   ${col(C.bold, apply)}  ` +
          `${col(C.gray, `[+${maxCommon}]`)}  ` +
          `${fmtLabels(labels)}`,
      );
    }
  }

  // R7: Lean - multi-codepoint applies
  if (multiCodepoint.length > 0) {
    const byApply = groupByApply(multiCodepoint);
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  Lean symbols - multi-codepoint applies ` +
          `(${byApply.size} sequences, ${multiCodepoint.length} entries):`,
      )}`,
    );
    for (const [apply, labels] of byApply) {
      const cps = [...apply].map((c) => fmtCp(c)).join(", ");
      console.log(
        `   ${col(C.bold, apply)}  ${col(C.gray, `[${cps}]`)}  ${fmtLabels(
          labels,
        )}`,
      );
    }
  }

  // R8a: Characters in both symbols.json AND Lean
  const sharedChars = [...baseApplyToLabels.entries()]
    .filter(([apply]) => leanApplyToLabels.has(apply))
    .map(([apply, baseLabelsSet]) => ({
      apply,
      baseLabels: [...baseLabelsSet], // Now an array from the Set
      leanLabels: [...leanApplyToLabels.get(apply)!],
    }));

  if (sharedChars.length > 0) {
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  Characters in both symbols.json and Lean (${sharedChars.length}):`,
      )}`,
    );
    console.log(
      `   ${"char".padEnd(5)} ${"U+".padEnd(8)} ${"base labels".padEnd(
        28,
      )} lean labels`,
    );
    console.log(`   ${"─".repeat(80)}`);
    for (const { apply, baseLabels, leanLabels } of sharedChars) {
      const cp = fmtCp(apply);

      // Join aliases with a comma. (Avoid fmtLabels here so ANSI codes don't break padEnd length)
      const baseLabelStr = baseLabels.join(", ");

      console.log(
        `   ${apply.padEnd(5)} ${cp.padEnd(8)} ${baseLabelStr.padEnd(
          28,
        )} ${fmtLabels(leanLabels)}`,
      );
    }
  }

  // R8b: symbols.json entries absent from Lean
  const leanAppliesSet = new Set(leanApplyToLabels.keys());
  const leanLabelsSet = new Set<string>();
  for (const labels of leanApplyToLabels.values()) {
    for (const l of labels) leanLabelsSet.add(l);
  }

  const baseOnlyBoth = base.filter(
    (s) => !leanLabelsSet.has(s.label) && !leanAppliesSet.has(s.apply),
  );
  const baseOnlyLabelOnly = base.filter(
    (s) => !leanLabelsSet.has(s.label) && leanAppliesSet.has(s.apply),
  );
  const baseOnlyApplyOnly = base.filter(
    (s) => leanLabelsSet.has(s.label) && !leanAppliesSet.has(s.apply),
  );

  if (baseOnlyBoth.length > 0) {
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  symbols.json entries absent from Lean entirely - label AND character (${baseOnlyBoth.length}):`,
      )}`,
    );
    for (const s of baseOnlyBoth)
      console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
  }
  if (baseOnlyLabelOnly.length > 0) {
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  symbols.json entries whose label is not in Lean, but character is (${baseOnlyLabelOnly.length}):`,
      )}`,
    );
    for (const s of baseOnlyLabelOnly)
      console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
  }
  if (baseOnlyApplyOnly.length > 0) {
    console.log(
      `\n${col(
        C.cyan,
        `${ICONS.info}  symbols.json entries whose character is not in Lean, but label is (${baseOnlyApplyOnly.length}):`,
      )}`,
    );
    for (const s of baseOnlyApplyOnly)
      console.log(`   ${s.label.padEnd(25)} ${s.apply}`);
  }
  if (
    baseOnlyBoth.length === 0 &&
    baseOnlyLabelOnly.length === 0 &&
    baseOnlyApplyOnly.length === 0
  ) {
    console.log(
      `${ICONS.ok}  All symbols.json entries have both label and character present in Lean`,
    );
  }

  // R8c: Preview of new symbols added from Lean
  const fromLean = symbols.length - base.length;
  console.log(`\n${fromLean} new symbols added from Lean table (first 20):`);
  for (const s of symbols.slice(base.length, base.length + 20)) {
    console.log(
      `   ${s.label.padEnd(10)} ${s.apply}  cat=${
        s.symbolPanelCategory ?? "hidden"
      }`,
    );
  }
  if (fromLean > 20) console.log(`   ... and ${fromLean - 20} more`);
}
