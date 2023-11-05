import { Uri, WorkspaceConfiguration, commands, env, window } from "vscode";
import { exec } from "child_process";
import path = require("path");
import { Version, versionFromString } from "./version";
import { versionEquals, versionGreaterThan } from "./version-compare";

export type VersionError = {
    reason: string;
}

function isVersionError(input: Version | VersionError): input is VersionError {
    return (input as VersionError).reason !== undefined;
}

const DOWNLOAD_INSTALLER = "Download Installer";
const OPEN_README = "Open README (Instructions)";
const OPEN_SETTINGS = "Open Settings";

export class VersionChecker {
    private _foundLspVersion: Version;
    private _foundLspBinary: boolean;
    private _wpPath: string | undefined;

    private _requiresVersionGreaterThan: boolean;
    private _requiredVersion: Version;

    constructor(configuration: WorkspaceConfiguration, desiredVersionString: string) {
        this._wpPath = configuration.get<string>("path");

        this._foundLspBinary = false;
        this._foundLspVersion = new Version(0, 0, 0);

        this._requiresVersionGreaterThan = desiredVersionString.slice(0, 2) == ">=";
        this._requiredVersion = versionFromString(desiredVersionString.substring(2));
    }

    public async run() {
        const version = await this.checkBinary();
        if (isVersionError(version)) {
            this._foundLspBinary = false;
        } else {
            this._foundLspVersion = version;
            this._foundLspBinary = true;
        }

        if (this._foundLspBinary) {
            if (this.needsUpdate()) {
                this.informUpdateAvailable()
            }
        } else {
            this.informWaterproofPathInvalid();
        }
    }

    private async checkBinary(): Promise<Version | VersionError> {
        return new Promise((resolve, reject) => {
            if (this._wpPath === undefined) return resolve({reason: "Waterproof.path is undefined"});
            const command = `${this._wpPath} --version`;

            exec(command, (err, stdout, stderr) => {
                if (err) return resolve({reason: err.message});
                resolve(versionFromString(stdout.trim()));
            });
        });
    }

    public get coqLspVersion(): Version {
        return this._foundLspVersion;
    }

    public get isWaterproofPathValid(): boolean {
        return this._foundLspBinary;
    }

    private needsUpdate(): boolean {
        if (this._requiresVersionGreaterThan) {
            return !versionGreaterThan(this._requiredVersion, this._foundLspVersion);
        } else {
            return !versionEquals(this._requiredVersion, this._foundLspVersion);
        }
    }

    private informUpdateAvailable() {
        const message = `This version of the Waterproof extension requires version ${this._requiredVersion.toString()}${this._requiresVersionGreaterThan ? " or above" : ""}, but we found ${this._foundLspVersion.toString()}.\nUse the button below to download a new installer.`
        window.showErrorMessage(message, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
    }

    private handleDownloadInstaller(value: typeof DOWNLOAD_INSTALLER | undefined) {
        env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-dependencies-installer"));
    }

    private informWaterproofPathInvalid() {
        const message = "Waterproof Path setting does not point to a valid location.";
        window.showErrorMessage(message, OPEN_SETTINGS, OPEN_README).then(this.handleInvalidPath);
    }

    private handleInvalidPath(value: typeof OPEN_README | typeof OPEN_SETTINGS | undefined) {
        switch (value) {
            case OPEN_README:
                env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-vscode#waterproof"));
                break;
            case OPEN_SETTINGS:
                commands.executeCommand("workbench.action.openSettings", "waterproof.path");
                break;
        }
    }
}


// export const checkCoqVersionUsingBinary = (): Promise<VersionObject> => {
//     const wpPath = path.parse(configuration().get("path") as string);
//     const coqcBinary = path.join(wpPath.dir, "coqc");
//     const command = `${coqcBinary} --version`;
//     const regex = /version (?<version>\d+\.\d+\.\d+)/g;
//     return new Promise((resolve, reject) => {
//         exec(command, (err, stdout, stderr) => {
//             if (err) reject(err.message);
//             const groups = regex.exec(stdout)?.groups;
//             if (groups === undefined) reject("Regex matching on version string went wrong");
//             //FIXME: ts-ignore;
//             //@ts-ignore
//             resolve({software: "coq", version: versionFromString(groups["version"])});
//         });
//     });
// }