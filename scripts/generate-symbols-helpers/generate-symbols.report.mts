import type { ReportContext } from "./generate-symbols.types.mts";
import {
  C,
  col,
  hint,
  fmtLabels,
  groupByApply,
  pairs,
  commonPrefixLen,
} from "./generate-symbols.utils.mts";

export function runReports(ctx: ReportContext): void {
  const {
    report,
    symbols,
    latexApplyToLabels,
    latexLabelToApply,
    latexBraceLabels,
    leanLabelStrategy,
    VERBOSE,
  } = ctx;

  const ICONS = {
    warn: "\u26A0\uFE0F",
    ok: "\u2705",
    info: "\u2139\uFE0F",
  };

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
        )} ${col(C.gray, "(every lean-only character had at most one eligible label)")}`,
      );
    } else {
      console.log(
        `\n${col(
          C.yellow,
          `${ICONS.warn}  Lean label strategy "${leanLabelStrategy}" - labels dropped from lean-only characters (${report.filteredLean.length} characters, ${totalDropped} labels dropped):`,
        )}`,
      );
      for (const r of report.filteredLean) {
        const cp = `U+${r.apply
          .codePointAt(0)!
          .toString(16)
          .toUpperCase()
          .padStart(4, "0")}`;
        console.log(
          `   ${col(C.bold, r.apply)} ${col(C.gray, cp)}  ` +
            `${col(C.gray, "kept:")} ${col(C.green, fmtLabels(r.keptLabels))}  ` +
            `${col(C.gray, "dropped:")} ${col(C.red, fmtLabels(r.droppedLabels))}`,
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
  const finalByApply = new Map<string, string[]>();
  for (const s of symbols) {
    if (!finalByApply.has(s.apply)) finalByApply.set(s.apply, []);
    finalByApply.get(s.apply)!.push(s.label);
  }

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
          `${ICONS.info}  Label resolves to different character than in LaTeX (${byApply.size} chars, ${differApplyItems.length} labels):`,
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
          `${ICONS.info}  LaTeX uses a different command for same character (${byApply.size} chars, ${diffCmdItems.length} labels):`,
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
  const labelsByApply = new Map<string, string[]>();
  for (const s of symbols) {
    if (!labelsByApply.has(s.apply)) labelsByApply.set(s.apply, []);
    labelsByApply.get(s.apply)!.push(s.label);
  }

  const prefixReport: Array<{
    apply: string;
    labels: string[];
    maxCommon: number;
  }> = [];
  for (const [apply, labels] of labelsByApply) {
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
        `${ICONS.info}  Aliases with matching prefixes - ranked by prefix length (${prefixReport.length} characters):`,
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
}
