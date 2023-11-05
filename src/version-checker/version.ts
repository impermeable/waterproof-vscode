export class Version {
    private _major: number;
    private _minor: number; 
    private _patch: number;

    constructor(major: number, minor: number, patch: number) {
        this._major = major;
        this._minor = minor;
        this._patch = patch;
    }

    public get major() { return this._major; }
    public get minor() { return this._minor; }
    public get patch() { return this._patch; }

    public toString() {
        return `${this._major}.${this._minor}.${this._patch}`;
    }
}

export const versionFromString = (version: string): Version => {
    const vs = version.split(".");
    if (vs.length < 3) throw Error("Invalid version system");
    
    return new Version(
        Number.parseInt(vs[0]), 
        Number.parseInt(vs[1]), 
        Number.parseInt(vs[2])
    );
}