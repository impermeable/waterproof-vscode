import { ExtensionContext, Uri, WorkspaceConfiguration, commands, env, window } from "vscode";
import { exec, spawn } from "child_process";
import path = require("path");
import { Version, VersionRequirement } from "./version";
import { COMPARE_MODE } from "./types";

export type VersionError = {
    reason: string;
}

/** Check if `input` is a version error. */
function isVersionError(input: any | VersionError): input is VersionError {
    return (input as VersionError).reason !== undefined;
}

const DOWNLOAD_INSTALLER = "Download Installer";
const OPEN_INSTRUCTIONS = "Installation Instructions";
const OPEN_README = "Open Readme";

export class VersionChecker {
    private _wpPath: string | undefined;
    private _context: ExtensionContext;

    private _reqVersionCoqLSP: VersionRequirement;
    private _reqVersionCoqWP: VersionRequirement;

    constructor(configuration: WorkspaceConfiguration, context: ExtensionContext, coqLspVersion: string, coqWaterproofVersion: string) {
        this._context = context;
        this._wpPath = configuration.get<string>("path");

        this._reqVersionCoqLSP = VersionRequirement.fromString(coqLspVersion);
        this._reqVersionCoqWP = VersionRequirement.fromString(coqWaterproofVersion);

    }

    /**
     * Run version checks that should happen *before* the extension launches. 
     * 
     * This call should likely be awaited.
     * 
     * @returns `Promise<boolean>` where the boolean indicates whether we can start the extension.
     */
    public async prelaunchChecks(): Promise<boolean> {
        const version = await this.checkLSPBinary();
        if (!isVersionError(version)) {
            if (version.needsUpdate(this._reqVersionCoqLSP)) {
                this.informUpdateAvailable("coq-lsp", this._reqVersionCoqLSP, version);
            }
        } else {
            // const message = "Waterproof\n\nThe Waterproof extension can not function without downloading additional software.\nIf you have not already done so, please download and execute the waterproof installer using the buttons below.";
            // window.showInformationMessage(message, { modal: true}, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
            
            
            this.informWaterproofPathInvalid();
            
            return Promise.resolve(false);
        }
        return Promise.resolve(true);
    }

    /**
     * Run version checks asynchronously.
     */
    public async run(): Promise<void> {
        const coqResult = await this.checkCoqVersionUsingBinary();
        const coqWaterproofResult = await this.checkWaterproofLib();

        if (isVersionError(coqWaterproofResult) || isVersionError(coqResult)) {
            if (isVersionError(coqWaterproofResult)) {
                this.informWaterproofLibNotFound();
            } else {
                // TODO: Only check when default coq syntax is not set.
                const coqWPversion = coqWaterproofResult.wpVersion;
                if (coqWPversion.needsUpdate(this._reqVersionCoqWP)) {
                    this.informUpdateAvailable("coq-waterproof", this._reqVersionCoqWP, coqWPversion);
                }
            }

            if (isVersionError(coqResult)) {
                this.informWaterproofPathInvalid();
            }
        } else {
            const wpV = coqWaterproofResult.wpVersion;
            if (wpV.needsUpdate(this._reqVersionCoqWP)) {
                this.informUpdateAvailable("coq-waterproof", this._reqVersionCoqWP, wpV);
            }
            const coqRequirement = new VersionRequirement(coqWaterproofResult.requiredCoqVersion, COMPARE_MODE.STRICT_EQUALS);
            if (coqResult.needsUpdate(coqRequirement)) {
                this.informUpdateAvailable("coq", coqRequirement, coqResult);
            }
        }
    }

    /**
     * Check installed version of coq using coqc.
     * @returns 
     */
    public async checkCoqVersionUsingBinary(): Promise<Version | VersionError> {
        return new Promise((resolve, reject) => {
            if (this._wpPath === undefined) return resolve({ reason: "Waterproof.path is undefined" });
            const coqcBinary = path.join(path.parse(this._wpPath).dir, "coqc");
            const command = `${coqcBinary} --version`;
            const regex = /version (?<version>\d+\.\d+\.\d+)/g;

            exec(command, (err, stdout, stderr) => {
                if (err) resolve({ reason: err.message });
                const groups = regex.exec(stdout)?.groups;
                if (groups === undefined) reject("Regex matching on version string went wrong");
                // FIXME: ts-ignore
                //@ts-ignore
                resolve(Version.fromString(groups["version"]));
            });
        });
    }

    /**
     * Check the version of coq-waterproof. 
     * @returns 
     */
    public async checkWaterproofLib(): Promise<{ wpVersion: Version, requiredCoqVersion: Version } | VersionError> {
        return new Promise((resolve, reject) => {
            if (this._wpPath === undefined) return resolve({ reason: "Waterproof.path is undefined" });
            const ext = process.platform === "win32" ? ".exe" : "";
            const coqtopPath = path.join(path.parse(this._wpPath).dir, `coqtop${ext}`);

            const printVersionFile = Uri.joinPath(this._context.extensionUri, "misc-includes", "printversion.v").fsPath;
            const command = `${coqtopPath} -l ${printVersionFile} -set "Coqtop Exit On Error" -batch`;
            exec(command, (err, stdout, stderr) => {
                if (err) return resolve({ reason: err.message });

                const [wpVersion, reqCoqVersion] = stdout.trim().split("+");
                const versionCoqWaterproof = Version.fromString(wpVersion);
                const versionRequiredCoq = Version.fromString(reqCoqVersion);

                resolve({ wpVersion: versionCoqWaterproof, requiredCoqVersion: versionRequiredCoq });
            });
        });
    }

    /**
     * Checks a) whether we can find the coq-lsp binary at the supplied location and b) returns the version of the installed version of coq-lsp.
     * @returns A promise containing either the Version of coq-lsp we found or a VersionError containing an error message.
     */
    private async checkLSPBinary(): Promise<Version | VersionError> {
        return new Promise((resolve, reject) => {
            if (this._wpPath === undefined) return resolve({ reason: "Waterproof.path is undefined" });
            const command = `${this._wpPath} --version`;

            exec(command, (err, stdout, stderr) => {
                if (err) return resolve({ reason: err.message });
                const version = Version.fromString(stdout.trim());
                resolve(version);
            });
        });
    }

    /**
     * Inform the user that we could not find the coq-waterproof library.
     */
    private informWaterproofLibNotFound() {
        const message = `Waterproof\n\nWe could not find a required library.\nUse the button below to download a new installer.`;
        window.showErrorMessage(message, { modal: true }, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
    }

    /**
     * Inform the user that their software does not satisfy the extension requirements.
     * @param software The name of the software we checked and found was not as required.
     * @param requirement The requirement that needed satisfying.
     * @param found The version we found.
     */
    private informUpdateAvailable(software: string, requirement: VersionRequirement, found: Version) {
        const platform = getPlatformHelper();
        if (platform === "macos" || platform == "windows") {
            const message = `This version of the Waterproof extension was created with version ${requirement.toEasyString()} of ${software} in mind, but we found ${found.toString()}.\nFor the best possible experience of Waterproof, we recommend using the correct version.\nUse the button below to download a new installer.`;
            window.showErrorMessage(message, { modal: true }, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
        } else {
            // We have no installer for other platforms, so we supply the user with the readme.
            const message = `This version of the Waterproof extension was created with version ${requirement.toEasyString()} of ${software} in mind, but we found ${found.toString()}.\nFor the best possible experience of Waterproof, we recommend using the correct version.\nUse the button below to open instructions on how to update.`;
            window.showErrorMessage(message, { modal: true }, OPEN_README).then(this.handleOpenReadme);
        }
    }

    private handleOpenReadme(value: typeof OPEN_README | undefined) {
        if (value === OPEN_README) env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-vscode#waterproof"));
    }

    /**
     * Helper that opens a website where the user can download a new installer.
     * @param value -
     */
    private handleDownloadInstaller(value: typeof DOWNLOAD_INSTALLER | undefined) {
        if (value === DOWNLOAD_INSTALLER) env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-dependencies-installer/releases/latest"));
    }

    /**
     * Inform the user that the Waterproof path is invalid.
     */
    private informWaterproofPathInvalid() {
        const message = "Waterproof\n\nWaterproof can't find everything it needs to properly function.\nFor more information on how to make the waterproof extension work, please see the installation instructions.";
        window.showErrorMessage(message, { modal: true }, OPEN_INSTRUCTIONS).then(this.handleInvalidPath);
    }

    /**
     * Handle the options for the invalid waterproof path message.
     * @param value -
     */
    private handleInvalidPath(value: typeof OPEN_INSTRUCTIONS | undefined) {
        if (value == OPEN_INSTRUCTIONS) {
            commands.executeCommand(`workbench.action.openWalkthrough`, `waterproof-tue.waterproof#waterproof.setup.${getPlatformHelper()}`, false);
        }
    }
}

const getPlatformHelper = () => {
    switch (process.platform) {
        case "aix": return "unknown";
        case "android": return "unknown";
        case "darwin": return "macos";
        case "freebsd": return "unknown";
        case "haiku": return "unknown";
        case "linux": return "linux";
        case "openbsd": return "unknown";
        case "sunos": return "unknown";
        case "win32": return "windows";
        case "cygwin": return "windows";
        case "netbsd": return "unknown";
    }
}