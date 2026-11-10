import type {
  DocChange,
  WrappingDocChange,
} from "@impermeable/waterproof-editor";

/**
 * Helpers for keeping the editor webview and the text document in sync.
 *
 * The extension keeps track of the text that the webview shows. Changes from the webview are
 * expressed in offsets into that text. When the document has meanwhile been changed by someone
 * else (a text editor, save actions, other extensions), these offsets are mapped onto the
 * current document text before the change is applied.
 */

/** Applies a change from the webview to `text`, which must be the text the change is based on. */
export function applyDocChange(
  text: string,
  change: DocChange | WrappingDocChange,
): string {
  const edits =
    "firstEdit" in change ? [change.firstEdit, change.secondEdit] : [change];
  // The edits of a wrapping change are both expressed in offsets into `text`; apply them from
  // the back so that applying one does not shift the other.
  return [...edits]
    .sort((a, b) => b.startInFile - a.startInFile)
    .reduce(
      (acc, e) =>
        acc.slice(0, e.startInFile) + e.finalText + acc.slice(e.endInFile),
      text,
    );
}

/**
 * Maps a change that is based on `base` onto `current`.
 *
 * The difference between the two texts is taken to be the single range between their common
 * prefix and their common suffix. Changes before or after that range are moved accordingly;
 * changes that overlap it conflict with the other change, and `undefined` is returned.
 */
export function mapDocChange<C extends DocChange | WrappingDocChange>(
  change: C,
  base: string,
  current: string,
): C | undefined {
  if (base === current) return change;

  const maxCommon = Math.min(base.length, current.length);
  let prefix = 0;
  while (prefix < maxCommon && base[prefix] === current[prefix]) prefix++;
  let suffix = 0;
  while (
    suffix < maxCommon - prefix &&
    base[base.length - 1 - suffix] === current[current.length - 1 - suffix]
  )
    suffix++;

  const changedEnd = base.length - suffix;
  const shift = current.length - base.length;

  const mapOne = (e: DocChange): DocChange | undefined => {
    if (e.endInFile <= prefix) return e;
    if (e.startInFile >= changedEnd)
      return {
        startInFile: e.startInFile + shift,
        endInFile: e.endInFile + shift,
        finalText: e.finalText,
      };
    return undefined;
  };

  if ("firstEdit" in change) {
    const firstEdit = mapOne(change.firstEdit);
    const secondEdit = mapOne(change.secondEdit);
    if (!firstEdit || !secondEdit) return undefined;
    return { firstEdit, secondEdit } as C;
  }
  return mapOne(change) as C | undefined;
}
