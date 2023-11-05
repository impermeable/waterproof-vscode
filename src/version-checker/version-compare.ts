import { Version } from "./version"

export const versionGreaterThan = (desired: Version, installed: Version): boolean => {
    return (
        installed.major >= desired.major  &&
        installed.minor >= desired.minor 
    );
}

export const versionEquals = (desired: Version, installed: Version): boolean => {
    return (
        installed.major == desired.major  &&
        installed.minor == desired.minor  &&
        installed.patch == desired.patch 
    );
}

export const versionEqualsIgnorePatch = (desired: Version, installed: Version): boolean => {
    return (desired.major == installed.major && desired.minor == installed.minor);
}