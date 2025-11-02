import { ExtensionContext, Uri, commands, env, window } from "vscode";
import { Version, VersionRequirement } from "./version";
import { WaterproofConfigHelper, WaterproofFileUtil, WaterproofSetting, WaterproofLogger as wpl } from "../helpers";

export type VersionError = {
    reason: string;
}

/** Check if `input` is a version error. */
function isVersionError(input: unknown) : input is VersionError {
    return (input as VersionError).reason !== undefined;
}

const DOWNLOAD_INSTALLER = "Download Installer";
const AUTO_INSTALL = "Automatically Install"; //Consider a clearer message
const OPEN_INSTRUCTIONS = "Installation Instructions";
const OPEN_README = "Open Readme";

export class VersionChecker {
    private _wpPath: string | undefined;
    private _context: ExtensionContext;

    private _reqVersionCoqLSP: VersionRequirement;
    private _reqVersionCoqWP: VersionRequirement;

    constructor(context: ExtensionContext, coqLspVersion: string, coqWaterproofVersion: string) {
        this._context = context;
        this._wpPath = WaterproofConfigHelper.get(WaterproofSetting.Path);

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
        wpl.log(`Version of coq-lsp: ${version}`);
        if (!isVersionError(version)) {
            if (version.needsUpdate(this._reqVersionCoqLSP)) {
                this.informUpdateAvailable("coq-lsp", this._reqVersionCoqLSP, version);
            }
        } else {

            this.informWaterproofPathInvalid();

            return Promise.resolve(false);
        }
        return Promise.resolve(true);
    }

    /**
     * Run version checks asynchronously.
     */
    public async run(): Promise<void> {
        const coqWaterproofResult = await this.checkWaterproofLib();

        if (isVersionError(coqWaterproofResult)) {
            this.informWaterproofLibNotFound();
        } else {
            const wpV = coqWaterproofResult.wpVersion;
            if (wpV.needsUpdate(this._reqVersionCoqWP)) {
                this.informUpdateAvailable("coq-waterproof", this._reqVersionCoqWP, wpV);
            }
        }
    }

    /**
     * Check the version of coq-waterproof.
     * @returns
     */
    public async checkWaterproofLib(): Promise<{ wpVersion: Version, requiredCoqVersion: Version } | VersionError> {
        if (this._wpPath === undefined) return { reason: "Waterproof.path is undefined" };
        const ext = process.platform === "win32" ? ".exe" : "";
        const ocamlfindPath = WaterproofFileUtil.join(WaterproofFileUtil.getDirectory(this._wpPath), `ocamlfind${ext}`);
        // If the user installed in a location different from the usual one, we need to set OCAMLFIND_CONF
        // This file is created by the installer
        const findlib_conf = WaterproofFileUtil.join(WaterproofFileUtil.getDirectory(this._wpPath), `findlib.conf`);
        const needEnv = getPlatformHelper() === "windows" &&
            this._wpPath !== this._context.extension.packageJSON.defaultCoqLspPathWindows;
        const extra_env = needEnv ? { OCAMLFIND_CONF: findlib_conf } : {};
        wpl.debug(`ocamlfindPath: ${ocamlfindPath}`);
        const command = `${ocamlfindPath} query -format %v coq-waterproof.plugin`;

        try {
            const stdout = await this.exec(command, extra_env);
            wpl.log(`Waterproof version: ${stdout}`);
            const [wpVersion, reqCoqVersion] = stdout.trim().split("+");
            const versionCoqWaterproof = Version.fromString(wpVersion);
            const versionRequiredCoq = Version.fromString(reqCoqVersion);
            return { wpVersion: versionCoqWaterproof, requiredCoqVersion: versionRequiredCoq };
        } catch (err: unknown) {
            return err instanceof Error
                ? { reason: err.message }
                : { reason: "Unknown error" };
        }
    }

    /**
     * Checks a) whether we can find the coq-lsp binary at the supplied location and b) returns the version of the installed version of coq-lsp.
     * @returns A promise containing either the Version of coq-lsp we found or a VersionError containing an error message.
     */
    private async checkLSPBinary(): Promise<Version | VersionError> {
        if (this._wpPath === undefined) return { reason: "Waterproof.path is undefined" };
        const command = `${this._wpPath} --version`;

        try {
            const stdout = await this.exec(command);
            const version = Version.fromString(stdout.trim());
            return version;
        } catch (err: unknown) {
            return err instanceof Error
                ? { reason: err.message }
                : { reason: "Unknown error" };
        }
    }

    /** Wrapper around shellIntegration  */
    private async exec(command: string, extra_env? : NodeJS.ProcessEnv): Promise<string> {
        wpl.log(`Running command: ${command}`)
        return new Promise((resolve, reject) => {
            // We use require here to avoid issues with the import statement in the browser context.
            // eslint-disable-next-line @typescript-eslint/no-require-imports
            const { exec } = require("child_process");
            exec(command, {
                env: { ...process.env, ...(extra_env ?? {}) }
            }, (err: { message: string; }, stdout: string, _stderr: unknown) => {
                if (err) {
                    reject({ reason: err.message });
                } else {
                    resolve(stdout);
                }
            });

        });
    }

    /**
     * Currently an autoinstaller only exists for Windows. If other platforms have a developed auto-installer, update this function
     */
    private platformHasAutoInstaller(){
        const platform = getPlatformHelper();
        if (platform == "windows") {
            return true
        } else {
            return false
        }
    }

    /**
     * Inform the user that we could not find the coq-waterproof library.
     */
    private informWaterproofLibNotFound() {
        const message_installer = "Waterproof\n\nWe could not find a required library, in particular the coq-waterproof library.\nUse the button below to download a new installer.";
        const message_no_installer = "Waterproof\n\nWe could not find a required library, in particular the `coq-waterproof` library.\nFor more information on how to make the waterproof extension work see the installation instructions.";
        if (this.platformHasAutoInstaller() && env.remoteName === undefined){
            window.showInformationMessage(message_installer, { modal: true }, AUTO_INSTALL, OPEN_INSTRUCTIONS).then(this.handleAutoInstallOrInstructions);
        } else {
            window.showInformationMessage(message_no_installer, { modal: true }, OPEN_INSTRUCTIONS).then(this.handleAutoInstallOrInstructions);
        }
    }

    /**
     * Inform the user that their software does not satisfy the extension requirements.
     * @param software The name of the software we checked and found was not as required.
     * @param requirement The requirement that needed satisfying.
     * @param found The version we found.
     */
    private informUpdateAvailable(software: string, requirement: VersionRequirement, found: Version) {
        const platform = getPlatformHelper();
        if (platform == "windows" && env.remoteName === undefined) {
            const message = `This version of the Waterproof extension was created with version ${requirement.toEasyString()} of ${software} in mind, but we found ${found.toString()}.\nFor the best possible experience of Waterproof, we recommend using the correct version.\nUse the button below to download a new installer.`;
            if (this.platformHasAutoInstaller()){
                window.showErrorMessage(message, { modal: true }, AUTO_INSTALL, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
            } else {
                window.showErrorMessage(message, { modal: true }, DOWNLOAD_INSTALLER).then(this.handleDownloadInstaller);
            }
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
    private handleDownloadInstaller(value: typeof AUTO_INSTALL | typeof DOWNLOAD_INSTALLER | undefined) {
        if (value === DOWNLOAD_INSTALLER){
            console.log("DOWNLOAD INSTALLER")
            env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-dependencies-installer/releases/"));
        } else if (value === AUTO_INSTALL){
            commands.executeCommand(`workbench.action.openWalkthrough`, `waterproof-tue.waterproof#waterproof.auto`, false);
        }
    }

    /**
     * Inform the user that the Waterproof path is invalid.
     */
    private informWaterproofPathInvalid() {
        const message_installer = "Waterproof\n\nWaterproof can't find everything it needs to properly function, in particular it doesn't seem to find the `coq-lsp` program.\nTry running the automatic installer, or for more information on how to make the waterproof extension work see the installation instructions.";
        const message_no_installer = "Waterproof\n\nWaterproof can't find everything it needs to properly function, in particular it doesn't seem to find the `coq-lsp` program. For more information on how to make the waterproof extension work see the installation instructions.";
        if (this.platformHasAutoInstaller()){
            window.showInformationMessage(message_installer, { modal: true }, AUTO_INSTALL, OPEN_INSTRUCTIONS).then(this.handleAutoInstallOrInstructions);
        } else {
            window.showInformationMessage(message_no_installer, { modal: true }, OPEN_INSTRUCTIONS).then(this.handleAutoInstallOrInstructions);
        }
    }

    /**
     * Handle the options for the invalid waterproof path message.
     * @param value -
     */
    private handleAutoInstallOrInstructions(value: typeof AUTO_INSTALL | typeof OPEN_INSTRUCTIONS | undefined) {
        console.log("Invalid Path Handler")
        if (value === OPEN_INSTRUCTIONS) {
            commands.executeCommand(`workbench.action.openWalkthrough`, `waterproof-tue.waterproof#waterproof.setup`, false);
        } else if (value === AUTO_INSTALL){
            commands.executeCommand(`workbench.action.openWalkthrough`, `waterproof-tue.waterproof#waterproof.auto`, false);
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