import {
    Disposable,
    ExtensionContext,
    Position,
    TextDocument,
    WorkspaceConfiguration,
    commands,
    workspace,
    window,
    ConfigurationTarget,
    Uri} from "vscode";
import { LanguageClientOptions, RevealOutputChannelOn } from "vscode-languageclient";

import { IExecutor, IGoalsComponent, IStatusComponent } from "./components";
import { CoqnitiveStatusBar } from "./components/enableButton";
import { CoqLspClient, CoqLspClientConfig, CoqLspClientFactory, CoqLspServerConfig } from "./lsp-client/clientTypes";
import { executeCommand } from "./lsp-client/commandExecutor";
import { CoqEditorProvider } from "./pm-editor";
import { checkConflictingExtensions, excludeCoqFileTypes } from "./util";
import { WebviewManager, WebviewManagerEvents } from "./webviewManager";
import { DebugPanel } from "./webviews/goalviews/debug";
import { GoalsPanel } from "./webviews/goalviews/goalsPanel";
import { Logbook } from "./webviews/goalviews/logbook";
import { SidePanelProvider, addSidePanel } from "./webviews/sidePanel";
import { CommonExecute } from "./webviews/standardviews/commonExecute";
import { ExecutePanel } from "./webviews/standardviews/execute";
import { SymbolsPanel } from "./webviews/standardviews/symbols";
import { TacticsPanel } from "./webviews/standardviews/tactics";

import { VersionChecker } from "./version-checker";
import { readFile } from "fs";
import { join as joinPath} from "path";
import { homedir } from "os";
import { WaterproofConfigHelper, WaterproofLogger } from "./helpers";
import { exec } from "child_process"
import { resolveSoa } from "dns";


export function activate(context: ExtensionContext): void {
    commands.executeCommand(`workbench.action.openWalkthrough`, `waterproof-tue.waterproof#waterproof.setup`, false);
}

/**
 * Main extension class
 */
export class Waterproof implements Disposable {

    /** The extension context */
    private readonly context: ExtensionContext;

    /** The resources that must be released when this extension is disposed of */
    private readonly disposables: Disposable[] = [];

    /** The function that can create a new Coq LSP client */
    private readonly clientFactory: CoqLspClientFactory;

    /** The manager for (communication between) webviews */
    public readonly webviewManager: WebviewManager;

    /**
     * The client that communicates with the Coq LSP server.
     * It's created by the `initializeClient` function.
     */
    public client!: CoqLspClient;

    /** The status bar item that indicates whether this extension is running */
    private readonly statusBar: IStatusComponent;

    /** The components that display or process the goals and messages on the current line */
    private readonly goalsComponents: IGoalsComponent[] = [];

    /** Main executor that allows for arbitrary execution */
    public readonly executorComponent: IExecutor;

    private sidePanelProvider: SidePanelProvider;

    /**
     * Constructs the extension lifecycle object.
     *
     * @param context the extension context object
     */
    constructor(context: ExtensionContext, clientFactory: CoqLspClientFactory) {
        checkConflictingExtensions();
        excludeCoqFileTypes();

        this.context = context;
        this.clientFactory = clientFactory;

        this.webviewManager = new WebviewManager();
        this.webviewManager.on(WebviewManagerEvents.editorReady, (document: TextDocument) => {
            this.client.updateCompletions(document);
        });
        this.webviewManager.on(WebviewManagerEvents.focus, (document: TextDocument) => {
            
            // update active document
            // only unset cursor when focussing different document (otherwise cursor position is often lost and user has to double click)
            if (this.client.activeDocument?.uri.toString() !== document.uri.toString()) {
                this.client.activeDocument = document;
                this.client.activeCursorPosition = undefined;
                for (const g of this.goalsComponents) g.updateGoals(undefined);
            }
            this.webviewManager.open("goals")
            // this.webviewManager.reveal("goals")
        });
        this.webviewManager.on(WebviewManagerEvents.cursorChange, (document: TextDocument, position: Position) => {
            // update active document and cursor
            this.client.activeDocument = document;
            this.client.activeCursorPosition = position;
            this.updateGoals(document, position);  // TODO: error handling
        });
        this.webviewManager.on(WebviewManagerEvents.command, (source: IExecutor, command: string) => {
            executeCommand(this.client, command).then(
                results => {
                    source.setResults(results);
                },
                (error: Error) => {
                    source.setResults(["Error: " + error.message]);  // (temp)
                }
            );
        });

        this.disposables.push(CoqEditorProvider.register(context, this.webviewManager));


        // make relevant gui components
        this.statusBar = new CoqnitiveStatusBar();
        var goalsPanel = new GoalsPanel(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration))
        this.goalsComponents.push(goalsPanel);
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.webviewManager.open("goals")
        this.webviewManager.addToolWebview("symbols", new SymbolsPanel(this.context.extensionUri));
        this.webviewManager.addToolWebview("commonExecute", new CommonExecute(this.context.extensionUri));
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.webviewManager.addToolWebview("tactics", new TacticsPanel(this.context.extensionUri));
        var logbook = new Logbook(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration));
        this.webviewManager.addToolWebview("logbook", logbook);
        this.goalsComponents.push(logbook);
        var debug = new DebugPanel(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration));
        this.webviewManager.addToolWebview("debug", debug);
        this.goalsComponents.push(debug);

        this.sidePanelProvider = addSidePanel(context, this.webviewManager);

        this.executorComponent = executorPanel;

        // register commands
        this.registerCommand("start", this.initializeClient);
        this.registerCommand("restart", this.restartClient);
        this.registerCommand("toggle", this.toggleClient);
        this.registerCommand("stop", this.stopClient);
        this.registerCommand("exportExerciseSheet", this.exportExerciseSheet);

        // Register the new Waterproof Document command
        this.registerCommand("newWaterproofDocument", this.newFileCommand);

        // FIXME: Move command handlers to their own location.

        this.registerCommand("openTutorial", this.waterproofTutorialCommand);

        this.registerCommand("pathSetting", () => {commands.executeCommand("workbench.action.openSettings", "waterproof.path");});
        this.registerCommand("argsSetting", () => {commands.executeCommand("workbench.action.openSettings", "waterproof.args");});
        this.registerCommand("defaultPath", () => {
            let defaultValue: string | undefined;
            switch (process.platform) {
                case "aix": defaultValue = undefined; break;
                case "android": defaultValue = undefined; break;
                // MACOS
                case "darwin": defaultValue = "/Applications/Waterproof_Background.app/Contents/Resources/bin/coq-lsp"; break;
                case "freebsd": defaultValue = undefined; break;
                case "haiku": defaultValue = undefined; break;
                // LINUX
                case "linux": defaultValue = "coq-lsp"; break;
                case "openbsd": defaultValue = undefined; break;
                case "sunos": defaultValue = undefined; break;
                // WINDOWS
                case "win32": defaultValue = "C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\bin\\coq-lsp.exe"; break;
                case "cygwin": defaultValue = undefined; break;
                case "netbsd": defaultValue = undefined; break;
            }
            if (defaultValue === undefined) {
                window.showInformationMessage("Waterproof has no known default value for this platform, please update the setting manually.");
                commands.executeCommand("workbench.action.openSettings", "waterproof.path");
            } else {
                try {
                    workspace.getConfiguration().update("waterproof.path", defaultValue, ConfigurationTarget.Global).then(() => {
                        setTimeout(() => {
                            WaterproofLogger.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.path.toString());
                            window.showInformationMessage(`Waterproof Path setting succesfully updated!`);
                        }, 100);
                    });
                } catch (e) {
                    console.error("Error in updating Waterproof.path setting:", e);
                }
            }
        });

        this.registerCommand("defaultArgsMac", () => {
            // If we are not on a mac platform, this is a no-op.
            // if (process.platform !== "darwin") { window.showErrorMessage("Waterproof: This setting should only be used on Mac platforms."); return; }

            const defaultArgs = [
                "--ocamlpath=/Applications/Waterproof_Background.app/Contents/Resources/lib",
                "--coqcorelib=/Applications/Waterproof_Background.app/Contents/Resources/lib/coq-core",
                "--coqlib=/Applications/Waterproof_Background.app/Contents/Resources/lib/coq"
            ];
            try {
                workspace.getConfiguration().update("waterproof.args", defaultArgs, ConfigurationTarget.Global).then(() => {
                    setTimeout(() => {
                        WaterproofLogger.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.args.toString());
                        
                        window.showInformationMessage(`Waterproof args setting succesfully updated!`);
                    }, 100);
                });
            } catch (e) {
                console.error("Error in updating Waterproof.args setting:", e);
            }
        });

        this.registerCommand("autoInstall", () => {
            commands.executeCommand(`waterproof.defaultPath`);

            const windowsInstallationScript = `echo Begin Waterproof Installation && curl -o Waterproof_Installer.exe -L 
                https://github.com/impermeable/waterproof-dependencies-installer/releases/download/v2.1.0%2B8.17/Waterproof-dependencies-installer-v2.1.0+8.17.exe 
                && echo Installer Finished Downloading && Waterproof_Installer.exe && echo Files Installed && del Waterproof_Installer.exe 
                && echo Refresh the Waterproof Checker to update libraries && echo This terminal can now be closed`
            const uninstallerLocation = `C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\Uninstall.exe`

            this.stopClient();

            let cmnd: string | undefined;
            switch (process.platform) {
                case "aix": cmnd = undefined; break;
                case "android": cmnd = undefined; break;
                // MACOS - This is currently not implemented, future task
                case "darwin": cmnd = undefined; break;
                case "freebsd": cmnd = undefined; break;
                case "haiku": cmnd = undefined; break;
                // LINUX - This is currently not implemented, issues when dealing with different distros and basic packages, installation is also easy enough 
                case "linux": cmnd = undefined; break;
                case "openbsd": cmnd = undefined; break;
                case "sunos": cmnd = undefined; break; 
                // WINDOWS
                case "win32":
                    // If a waterproof installation is found in the default location it is first uninstalled.
                    // The path is updated to the default location so if an installation is present in another directory it still will not be utilised
                    // The installer is then downloaded, run and then removed.
                case "cygwin": cmnd =  `start "WATERPROOF INSTALLER" cmd /k "IF EXIST ` + uninstallerLocation + ` (echo Uninstalling previous installation of Waterproof && ` 
                    + uninstallerLocation + ` && ` + windowsInstallationScript + ` ) ELSE (echo No previous installation found && ` +  windowsInstallationScript + ` )"`; break;
                case "netbsd": cmnd = undefined; break;
            }

            if (cmnd === undefined) {
                window.showInformationMessage("Waterproof has no automatic installation process for this platform, please refer to the walktrough page.");
            } else {
                this.autoInstall(cmnd)
            }  
        });
    }

    /**
     * Attempts to install all required libraries
     * @returns A promise containing either the Version of coq-lsp we found or a VersionError containing an error message.
     */
    private async autoInstall(command: string): Promise<Boolean> {
        return new Promise((resolve, reject) => {
            exec(command, (err, stdout, stderr) => {
                if (err) {
                    // Simple fixed scripts are run, the user is able to stop these but they are not considered errors 
                    // as the user has freedom to choose the steps and can rerun the command.
                } 
                this.initializeClient();
                resolve(true)
            });
        });
    }

    private async waterproofTutorialCommand(): Promise<void> {
        const defaultUri = workspace.workspaceFolders ? 
            Uri.file(joinPath(workspace.workspaceFolders[0].uri.fsPath, "waterproof_tutorial.mv")) : 
            Uri.file(joinPath(homedir(), "waterproof_tutorial.mv"));
        window.showSaveDialog({filters: {'Waterproof': ["mv", "v"]}, title: "Waterproof Tutorial", defaultUri}).then((uri) => {
            if (!uri) {
                window.showErrorMessage("Something went wrong in saving the Waterproof tutorial file");
                return;
            }
            const newFilePath = Uri.joinPath(this.context.extensionUri, "misc-includes", "waterproof_tutorial.mv").fsPath;
            readFile(newFilePath, (err, data) => {
                if (err) {
                    window.showErrorMessage("Could not a new Waterproof file.");
                    console.error(`Could not read Waterproof tutorial file: ${err}`);
                    return;
                }
                workspace.fs.writeFile(uri, data).then(() => {
                    // Open the file using the waterproof editor
                    // TODO: Hardcoded `coqEditor.coqEditor`.
                    commands.executeCommand("vscode.openWith", uri, "coqEditor.coqEditor");
                });
            })
        });
    }

    /**
     * Handle the newWaterproofDocument command. 
     * This command can be either activated by the user via the 'command palette' 
     * or by using the File -> New File... option. 
     */
    private async newFileCommand(): Promise<void> {
        const defaultUri = workspace.workspaceFolders ? 
            Uri.file(joinPath(workspace.workspaceFolders[0].uri.fsPath, "new_waterproof_document.mv")) : 
            Uri.file(joinPath(homedir(), "new_waterproof_document.mv"));
        window.showSaveDialog({filters: {'Waterproof': ["mv", "v"]}, title: "New Waterproof Document", defaultUri}).then((uri) => {
            if (!uri) {
                window.showErrorMessage("Something went wrong in creating a new waterproof document");
                return;
            }
            const newFilePath = Uri.joinPath(this.context.extensionUri, "misc-includes", "empty_waterproof_document.mv").fsPath;
            readFile(newFilePath, (err, data) => {
                if (err) {
                    window.showErrorMessage("Could not a new Waterproof file.");
                    console.error(`Could not read Waterproof tutorial file: ${err}`);
                    return;
                }
                workspace.fs.writeFile(uri, data).then(() => {
                    // Open the file using the waterproof editor
                    // TODO: Hardcoded `coqEditor.coqEditor`.
                    commands.executeCommand("vscode.openWith", uri, "coqEditor.coqEditor");
                });
            })
        });
    }

    /**
     * Registers a new Waterproof command and adds it to `disposables`.
     *
     * @param name the identifier for the command (after the "waterproof." prefix)
     * @param handler the function that runs when the command is executed
     * @param editorCommand whether to register a "text editor" or ordinary command
     */
    private registerCommand(name: string, handler: (...args: any[]) => void, editorCommand: boolean = false) {
        const register = editorCommand ? commands.registerTextEditorCommand : commands.registerCommand;
        this.disposables.push(register("waterproof." + name, handler, this));
    }

    /**
     * Remove solutions from document and open save dialog for the solution-less file.
     */
    async exportExerciseSheet() {
        const document = this.client.activeDocument;
        if (document) {
            let content = document.getText();
            const pattern = /<input-area>\s*```coq([\s\S]*?)\s*```\s<\/input-area>/g; 
            const replacement = `<input-area>\n\`\`\`coq\n(* Type your proof here *)\n\`\`\`\n</input-area>`;
            content = content.replace(pattern, replacement);
            const fileUri = await window.showSaveDialog();
            if (fileUri) {
                await workspace.fs.writeFile(fileUri, Buffer.from(content, 'utf8'));
                window.showInformationMessage(`Saved to: ${fileUri.fsPath}`);
            }
        }
    }

    /**
     * Create the lsp client and update relevant status components
     */
    async initializeClient(): Promise<void> {

        // Run the version checker.
        const requiredCoqLSPVersion = this.context.extension.packageJSON.requiredCoqLspVersion;
        const requiredCoqWaterproofVersion = this.context.extension.packageJSON.requiredCoqWaterproofVersion;
        const versionChecker = new VersionChecker(WaterproofConfigHelper.configuration, this.context, requiredCoqLSPVersion, requiredCoqWaterproofVersion);
        // 
        const foundServer = await versionChecker.prelaunchChecks();

        if (foundServer) {

            versionChecker.run();
            
            if (this.client?.isRunning()) {
                return Promise.reject(new Error("Cannot initialize client; one is already running."))
            }

            const serverOptions = CoqLspServerConfig.create(
                // TODO: Support +coqversion versions.
                this.context.extension.packageJSON.requiredCoqLspVersion.slice(2),
                WaterproofConfigHelper.configuration
            );

            const clientOptions: LanguageClientOptions = {
                documentSelector: [{ language: "coqmarkdown" }],  // only `.mv` files, not `.v`
                outputChannelName: "Waterproof LSP Events (Initial)",
                revealOutputChannelOn: RevealOutputChannelOn.Info,
                initializationOptions: serverOptions,
                markdown: { isTrusted: true, supportHtml: true },
            };

            this.client = this.clientFactory(clientOptions, WaterproofConfigHelper.configuration);
            return this.client.startWithHandlers(this.webviewManager).then(
                () => {
                    // show user that LSP is working
                    this.statusBar.update(true);
                },
                reason => {
                    const message = reason.toString();
                    console.error(`Error during client initialization: ${message}`);
                    this.statusBar.failed(message);
                    throw reason;  // keep chain rejected
                }
            );
        } else {
            this.statusBar.failed("LSP not found");
        }
    }

    /**
     * Restarts the Coq LSP client.
     */
    private async restartClient(): Promise<void> {
        await this.stopClient();
        await this.initializeClient();
    }

    /**
     * Toggles the state of the Coq LSP client. That is, stop the client if it's running and
     * otherwise initialize it.
     */
    private toggleClient(): Promise<void> {
        if (this.client?.isRunning()) {
            return this.stopClient();
        } else {
            return this.initializeClient();
        }
    }

    /**
     * Disposes of the Coq LSP client.
     */
    private async stopClient(): Promise<void> {
        if (this.client.isRunning()) {
            for (const g of this.goalsComponents) g.disable();
            await this.client.dispose(2000);
            this.statusBar.update(false);
        } else {
            return Promise.resolve();
        }
    }

    /**
     * This function gets called on TextEditorSelectionChange events and it requests the goals
     * if needed
     */
    private async updateGoals(document: TextDocument, position: Position): Promise<void> {
        if (!this.client.isRunning()) return;
        const params = this.client.createGoalsRequestParameters(document, position);
        for (const g of this.goalsComponents) g.goalRequestSent(params)
        this.client.requestGoals(params).then(
            response => {
                for (const g of this.goalsComponents) g.updateGoals(response)
            },
            reason => {
                for (const g of this.goalsComponents) g.failedGoals(reason);
            }
        );
    }

    dispose() {
        this.statusBar.dispose();
        this.stopClient();
        for (const d of this.disposables) {
            d.dispose();
        }
    }

}
