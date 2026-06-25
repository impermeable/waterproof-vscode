/**
 * Process Waterproof Rocq or Lean file content by removing solutions from input cells.
 * Finds input cells and replaces the content with empty code blocks.
 * Even if an input cell has several code blocks inside, the contents will be substituted with one empty code block.
 *
 * For rocq an input cell has the following form:
 * <input-area>
 * ```coq
 *
 * ....code....
 *
 * ```
 * </input-area>
 *
 * For lean an input cell has the following form:
 * :::input
 * ```lean
 *
 * ....code....
 *
 * ```
 * :::
 *
 * @param content - The raw content of a .mv or .lean file
 * @returns Processed content with solutions removed
 */
export function clearInputCells(content: string, extension: string): string {
  let pattern: RegExp;
  let replacement: string;
  switch (extension) {
    case ".lean":
      pattern = /:::input\s*```lean[\s\S]*?```\s*:::/g;
      replacement = ":::input\n```lean\n\n```\n:::";
      break;
    case ".mv":
      pattern = /<input-area>\s*```coq[\s\S]*?```\s*<\/input-area>/g;
      replacement = "<input-area>\n```coq\n\n```\n</input-area>";
      break;
    default:
      throw new Error(
        `Only files with extension .lean and .mv are supported, found ${extension}`,
      );
  }
  content = content.replace(pattern, replacement);
  return content;
}
