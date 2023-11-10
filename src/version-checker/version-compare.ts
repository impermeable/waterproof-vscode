import { NOT_SPECIFIED } from "./types";
import { Version } from "./version"

export const versionGreaterThan = (required: Version, installed: Version): boolean => {
    return (
        installed.major >= required.major  &&
        installed.minor >= required.minor 
    );
}

export const versionEquals = (required: Version, installed: Version): boolean => {
    if (required.patch === NOT_SPECIFIED) return versionEqualsIgnorePatch(required, installed);
    return (
        installed.major == required.major  &&
        installed.minor == required.minor  &&
        installed.patch == required.patch 
    );
}

export const versionEqualsIgnorePatch = (required: Version, installed: Version): boolean => {
    return (required.major == installed.major && required.minor == installed.minor);
}