/**
 * generate-symbols.utils.mts
 *
 * Pure utility functions and constants with no dependencies on the broader
 * generate-symbols pipeline. Used by the main script and various report/test modules.
 */

import type { LeanLabelStrategy } from "./generate-symbols.types.mts";

// -- ANSI color helpers --

export const C = {
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

export function col(color: string, text: string): string {
  return `${color}${text}${C.reset}`;
}

export function hint(msg: string): string {
  return col(C.dim, `(${msg})`);
}

// -- Helpers --

/** Strip a leading backslash to get the bare stem, used for length comparisons. */
export function stem(label: string): string {
  return label.startsWith("\\") ? label.slice(1) : label;
}

/** Common prefix length, ignoring leading backslash */
export function commonPrefixLen(a: string, b: string): number {
  const sa = stem(a);
  const sb = stem(b);
  let i = 0;
  while (i < sa.length && i < sb.length && sa[i] === sb[i]) i++;
  return i;
}

/** Format labels as a comma-separated string */
export function fmtLabels(labels: string[]): string {
  return labels.join(", ");
}

/** Group an array of {apply, label} items by apply, collecting labels */
export function groupByApply(
  items: ReadonlyArray<{ apply: string; label: string }>,
): Map<string, string[]> {
  const map = new Map<string, string[]>();
  for (const { apply, label } of items) {
    if (!map.has(apply)) map.set(apply, []);
    map.get(apply)!.push(label);
  }
  return map;
}

/** Returns all pairs from an array */
export function pairs(arr: string[]): [string, string][] {
  const result: [string, string][] = [];
  for (let i = 0; i < arr.length; i++)
    for (let j = i + 1; j < arr.length; j++) result.push([arr[i]!, arr[j]!]);
  return result;
}

// ---------------------------------------------------------------------------
// Lean label strategy filter
// ---------------------------------------------------------------------------

/**
 * Given a list of Lean labels for the same apply (unicode character), return
 * which labels to keep and which to drop according to the configured strategy.
 *
 *   "all"             - keep everything (no-op)
 *   "longest"         - keep the single longest label (by stem length)
 *   "shortest"        - keep the single shortest label (by stem length)
 *   "longest_prefix"  - group labels whose stems have a prefix relationship
 *                       (i.e. one stem is a prefix of another, such as
 *                       "superseteq" / "superseteqq") and keep the longest
 *                       within each group; isolated labels are always kept
 *   "shortest_prefix" - same grouping, keep the shortest in each group
 *
 * Ties in length are broken lexicographically so the result is deterministic.
 */
export function filterLeanLabels(
  labels: string[],
  strategy: LeanLabelStrategy,
): { kept: string[]; dropped: string[] } {
  if (strategy === "all" || labels.length <= 1) {
    return { kept: [...labels], dropped: [] };
  }

  // ── "longest" / "shortest": pick exactly one label globally ──────────────
  if (strategy === "longest" || strategy === "shortest") {
    const pickLongest = strategy === "longest";
    const sorted = [...labels].sort((a, b) => {
      const diff = stem(a).length - stem(b).length;
      if (diff !== 0) return pickLongest ? -diff : diff;
      return a.localeCompare(b);
    });
    return { kept: [sorted[0]!], dropped: sorted.slice(1) };
  }

  // ── "longest_prefix" / "shortest_prefix": group by prefix relationship ───
  // Two labels are in the same group iff one stem is a prefix of the other.
  // Groups are built with union-find so transitive chains are handled correctly
  // (e.g. \sub, \sube, \subseteq would all merge into one group).
  const pickLongest = strategy === "longest_prefix";
  const n = labels.length;

  // Union-Find with path compression
  const parent = Array.from({ length: n }, (_, i) => i);
  function find(x: number): number {
    while (parent[x] !== x) {
      parent[x] = parent[parent[x]!]!; // path halving
      x = parent[x]!;
    }
    return x;
  }
  function union(x: number, y: number): void {
    parent[find(x)] = find(y);
  }

  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      const a = stem(labels[i]!);
      const b = stem(labels[j]!);
      if (a.startsWith(b) || b.startsWith(a)) {
        union(i, j);
      }
    }
  }

  // Collect groups
  const groups = new Map<number, number[]>();
  for (let i = 0; i < n; i++) {
    const root = find(i);
    if (!groups.has(root)) groups.set(root, []);
    groups.get(root)!.push(i);
  }

  const kept: string[] = [];
  const dropped: string[] = [];

  for (const indices of groups.values()) {
    if (indices.length === 1) {
      // Singleton group - no prefix sibling, always keep
      kept.push(labels[indices[0]!]!);
      continue;
    }
    // Sort group members, winner goes first
    const sorted = [...indices].sort((a, b) => {
      const diff = stem(labels[a]!).length - stem(labels[b]!).length;
      if (diff !== 0) return pickLongest ? -diff : diff;
      return labels[a]!.localeCompare(labels[b]!);
    });
    kept.push(labels[sorted[0]!]!);
    for (let k = 1; k < sorted.length; k++) {
      dropped.push(labels[sorted[k]!]!);
    }
  }

  return { kept, dropped };
}
