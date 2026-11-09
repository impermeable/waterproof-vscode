import { NOT_SPECIFIED } from "./types";
import { Version } from "./version";

/**
 * Returns whether `installed` is greater than or equal to `required`,
 * comparing major, minor and patch in order.
 * An unspecified component in `required` (e.g. the patch in `>=3.1`) matches anything,
 * an unspecified component in `installed` is treated as 0.
 */
export const versionGreaterThan = (
  required: Version,
  installed: Version,
): boolean => {
  const pairs = [
    [required.major, installed.major],
    [required.minor, installed.minor],
    [required.patch, installed.patch],
  ] as const;
  for (const [req, inst] of pairs) {
    if (req === NOT_SPECIFIED) return true;
    const instNum = inst === NOT_SPECIFIED ? 0 : inst;
    if (instNum !== req) return instNum > req;
  }
  return true;
};

export const versionEquals = (
  required: Version,
  installed: Version,
): boolean => {
  if (required.patch === NOT_SPECIFIED)
    return versionEqualsIgnorePatch(required, installed);
  return (
    installed.major == required.major &&
    installed.minor == required.minor &&
    installed.patch == required.patch
  );
};

export const versionEqualsIgnorePatch = (
  required: Version,
  installed: Version,
): boolean => {
  return required.major == installed.major && required.minor == installed.minor;
};
