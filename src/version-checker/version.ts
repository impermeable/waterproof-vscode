import { COMPARE_MODE, NOT_SPECIFIED } from "./types";
import { versionEquals, versionGreaterThan } from "./version-compare";

export type VersionIdentifier = number | typeof NOT_SPECIFIED;

export class Version {
    private _major: VersionIdentifier;
    private _minor: VersionIdentifier;
    private _patch: VersionIdentifier;

    constructor(major: VersionIdentifier, minor: VersionIdentifier, patch: VersionIdentifier) {
        this._major = major;
        this._minor = minor;
        this._patch = patch;
    }

    public get major() { return this._major; }
    public get minor() { return this._minor; }
    public get patch() { return this._patch; }

    public get unknown() {
        return this._major === NOT_SPECIFIED &&
            this._minor === NOT_SPECIFIED &&
            this._patch === NOT_SPECIFIED;
    }

    /**
     * Returns true when this version is in need of updating to satisfy `requirement`. 
     * @param requirement The `VersionRequirement` this version must satisfy.
     */
    public needsUpdate(requirement: VersionRequirement): boolean {
        return !requirement.isSatisfiedBy(this);
    }

    public toString() {
        return `${this._major}.${this._minor}.${this._patch}`;
    }

    // TODO: We do not support non-numeric versions, eg. 0.3.5a is invalid.
    static fromString(version: string): Version {
        const vs = version.split(".").map((value) => Number.parseInt(value));
        const dotCount = vs.length - 1;

        if (dotCount < 0 || dotCount > 2) throw Error(`Unknown version system encountered '${version}.'`);
        switch (dotCount) {
            case 0:
                return new Version(vs[0], NOT_SPECIFIED, NOT_SPECIFIED);
            case 1:
                return new Version(vs[0], vs[1], NOT_SPECIFIED);
            case 2:
                return new Version(vs[0], vs[1], vs[2]);
        }

        return Version.unknown;
    }

    static get unknown(): Version {
        const ver = new Version(NOT_SPECIFIED, NOT_SPECIFIED, NOT_SPECIFIED);
        return ver;
    }
}

export class VersionRequirement {
    private _requiredVersion: Version;
    private _compareMode: COMPARE_MODE;

    constructor(requiredVersion: Version, compareMode: COMPARE_MODE) {
        this._requiredVersion = requiredVersion;
        this._compareMode = compareMode;
    }

    /**
     * Returns whether this requirement is satisfied by `version`.
     * @param version 
     */
    public isSatisfiedBy (version: Version): boolean {
        switch (this._compareMode) {
            case COMPARE_MODE.GREATER_THAN_EQUALS: 
                return versionGreaterThan(this._requiredVersion, version);
            case COMPARE_MODE.STRICT_EQUALS:
                return versionEquals(this._requiredVersion, version);
        }
    }

    public toEasyString() {
        return `${this._requiredVersion.toString()}${this._compareMode === COMPARE_MODE.GREATER_THAN_EQUALS ? " or above" : ""}`;
    }

    public toString() {
        return `${this._compareMode} ${this._requiredVersion.toString()}`;
    }

    static fromString(input: string): VersionRequirement {
        const mode = input.slice(0, 2);
        const rest = input.slice(2);
        switch (mode) {
            case COMPARE_MODE.GREATER_THAN_EQUALS:
                return new VersionRequirement(Version.fromString(rest), COMPARE_MODE.GREATER_THAN_EQUALS);
            case COMPARE_MODE.STRICT_EQUALS:
                return new VersionRequirement(Version.fromString(rest), COMPARE_MODE.STRICT_EQUALS);
            default:
                throw Error(`Unsupported version compare mode '${mode}'.`);
        }
    }
}