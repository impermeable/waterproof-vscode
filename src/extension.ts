import {
    Disposable,
    ExtensionContext,
    Position,
    TextDocument,
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
import { Search } from "./webviews/standardviews/search";
import { Help } from "./webviews/standardviews/help";
import { ExpandDefinition } from "./webviews/standardviews/expandDefinition";
import { ExecutePanel } from "./webviews/standardviews/execute";
import { SymbolsPanel } from "./webviews/standardviews/symbols";
import { TacticsPanel } from "./webviews/standardviews/tactics";

import { VersionChecker } from "./version-checker";
import { Utils } from "vscode-uri";
import { WaterproofConfigHelper, WaterproofLogger as wpl } from "./helpers";



export function activate(_context: ExtensionContext): void {
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

    private clientRunning: boolean = false;

    /**
     * Constructs the extension lifecycle object.
     *
     * @param context the extension context object
     */
    constructor(context: ExtensionContext, clientFactory: CoqLspClientFactory, private readonly _isWeb = false) {
        wpl.log("Waterproof initialized");
        checkConflictingExtensions();
        excludeCoqFileTypes();

        this.context = context;
        this.clientFactory = clientFactory;

        this.webviewManager = new WebviewManager();
        this.webviewManager.on(WebviewManagerEvents.editorReady, (document: TextDocument) => {
            this.client.updateCompletions(document);
        });
        this.webviewManager.on(WebviewManagerEvents.focus, async (document: TextDocument) => {
            wpl.log("Focus event received");

            // Wait for client to initialize
            if (!this.clientRunning) {
                console.warn("Focus event received before client is ready. Waiting...");
                const waitForClient = async (): Promise<void> => {
                    return new Promise(resolve => {
                        const interval = setInterval(() => {
                            if (this.clientRunning) {
                                clearInterval(interval);
                                resolve();
                            }
                        }, 100);
                    });
                };
                await waitForClient();
                wpl.log("Client ready. Proceeding with focus event.");
        	}

            wpl.log("Client state");

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
            if (command == "createHelp") {
                source.setResults(["createHelp"]);
            } else {
                executeCommand(this.client, command).then(
                    results => {
                        source.setResults(results);
                    },
                    (error: Error) => {
                        source.setResults(["Error: " + error.message]);  // (temp)
                    }
                );
            }
        });

        this.disposables.push(CoqEditorProvider.register(context, this.webviewManager));


        // make relevant gui components
        this.statusBar = new CoqnitiveStatusBar();
        const goalsPanel = new GoalsPanel(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration))
        this.goalsComponents.push(goalsPanel);
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.webviewManager.open("goals")
        this.webviewManager.addToolWebview("symbols", new SymbolsPanel(this.context.extensionUri));
        this.webviewManager.addToolWebview("search", new Search(this.context.extensionUri));
        this.webviewManager.addToolWebview("help", new Help(this.context.extensionUri));
        this.webviewManager.addToolWebview("expandDefinition", new ExpandDefinition(this.context.extensionUri));
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.webviewManager.addToolWebview("tactics", new TacticsPanel(this.context.extensionUri));
        const logbook = new Logbook(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration));
        this.webviewManager.addToolWebview("logbook", logbook);
        const debug = new DebugPanel(this.context.extensionUri, CoqLspClientConfig.create(WaterproofConfigHelper.configuration));
        this.webviewManager.addToolWebview("debug", debug);

        this.sidePanelProvider = addSidePanel(context, this.webviewManager);

        this.executorComponent = executorPanel;

        // register commands
        wpl.log("Calling initializeClient...");
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
                            wpl.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.path.toString());
                            window.showInformationMessage(`Waterproof Path setting succesfully updated!`);
                        }, 100);
                    });
                } catch (e) {
                    console.error("Error in updating Waterproof.path setting:", e);
                }
            }
        });
        this.registerCommand("setDefaultArgsWin", () => this.setDefaultArgsWin());

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
                        wpl.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.args.toString());

                        window.showInformationMessage(`Waterproof args setting succesfully updated!`);
                    }, 100);
                });
            } catch (e) {
                console.error("Error in updating Waterproof.args setting:", e);
            }
        });

        this.registerCommand("autoInstall", async () => {
            commands.executeCommand(`waterproof.defaultPath`);
            commands.executeCommand(`waterproof.setDefaultArgsWin`);

            const windowsInstallationScript = `echo Begin Waterproof Installation && echo Downloading installer ... && curl -o Waterproof_Installer.exe -L https://github.com/impermeable/waterproof-dependencies-installer/releases/download/v2.2.0%2B8.17/Waterproof-dependencies-installer-v2.2.0+8.17.exe && echo Installer Finished Downloading - Please wait for the Installer to execute, this can take up to a few minutes && Waterproof_Installer.exe && echo Required Files Installed && del Waterproof_Installer.exe && echo COMPLETE - The Waterproof checker will restart automatically a few seconds after this terminal is closed`
            const uninstallerLocation = `C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\Uninstall.exe`

            await this.stopClient();

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
                // eslint-disable-next-line no-fallthrough
                case "cygwin": cmnd =  `start "WATERPROOF INSTALLER" cmd /k "IF EXIST ` + uninstallerLocation + ` (echo Uninstalling previous installation of Waterproof && `
                    + uninstallerLocation + ` && ` + windowsInstallationScript + ` ) ELSE (echo No previous installation found && ` +  windowsInstallationScript + ` )"`; break;
                case "netbsd": cmnd = undefined; break;
            }

            if (cmnd === undefined) {
                window.showInformationMessage("Waterproof has no automatic installation process for this platform, please refer to the walktrough page.");
            } else {
                await this.autoInstall(cmnd)
            }
        });

        this.registerCommand("toggleInEditorLineNumbers", () => {
            const updated = !WaterproofConfigHelper.showLineNumbersInEditor;
            WaterproofConfigHelper.showLineNumbersInEditor = updated;
            window.showInformationMessage(`Waterproof: Line numbers in editor are now ${updated ? "shown" : "hidden"}.`);
        });
    }

    /**
     * Attempts to install all required libraries
     * @returns A promise containing either the Version of coq-lsp we found or a VersionError containing an error message.
     */
    private async autoInstall(command: string): Promise<boolean> {
        return new Promise((resolve, _reject) => {
            // Doing the require here to avoid issues with the import in the browser version
            // eslint-disable-next-line @typescript-eslint/no-require-imports
            const { exec } = require("child_process");
            exec(command, (err : unknown, _stdout: unknown, _stderr: unknown) => {
                if (err) {
                    // Simple fixed scripts are run, the user is able to stop these but they are not considered errors
                    // as the user has freedom to choose the steps and can rerun the command.
                }
                this.initializeClient();
                resolve(true)
            });
        });
    }

    /**
     * Sets the default args for the Waterproof extension on Windows, for when the installer is used with the default location
     */
    private async setDefaultArgsWin() : Promise<void> {
        const defaultArgs = [
            "--ocamlpath=C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\lib",
            "--coqcorelib=C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\lib\\coq-core",
            "--coqlib=C:\\cygwin_wp\\home\\runneradmin\\.opam\\wp\\lib\\coq"
        ];
        try {
            workspace.getConfiguration().update("waterproof.args", defaultArgs, ConfigurationTarget.Global).then(() => {
                setTimeout(() => {
                    wpl.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.args.toString());
                }, 100);
            });
        } catch (e) {
            console.error("Error in updating Waterproof.args setting:", e);
        }
    }

    private async waterproofTutorialCommand(): Promise<void> {
        const defaultUri = Utils.joinPath(workspace.workspaceFolders![0].uri, "waterproof_tutorial.mv");
        window.showSaveDialog({filters: {'Waterproof': ["mv", "v"]}, title: "Waterproof Tutorial", defaultUri}).then((uri) => {
            if (!uri) {
                window.showErrorMessage("Something went wrong in saving the Waterproof tutorial file");
                return;
            }
            const newFilePath = Uri.joinPath(this.context.extensionUri, "misc-includes", "waterproof_tutorial.mv");
            workspace.fs.readFile(newFilePath)
                .then((data) => {
                    workspace.fs.writeFile(uri, data).then(() => {
                        // Open the file using the waterproof editor
                        // TODO: Hardcoded `coqEditor.coqEditor`.
                        commands.executeCommand("vscode.openWith", uri, "coqEditor.coqEditor");
                    });                    
                }, (err) => {
                    window.showErrorMessage("Could not a new Waterproof file.");
                    console.error(`Could not read Waterproof tutorial file: ${err}`);
                    return;                   
                })
        });
    }

    /**
     * Handle the newWaterproofDocument command.
     * This command can be either activated by the user via the 'command palette'
     * or by using the File -> New File... option.
     */
    private async newFileCommand(): Promise<void> {
        const defaultUri = Utils.joinPath(workspace.workspaceFolders![0].uri, "new_waterproof_document.mv");
        window.showSaveDialog({filters: {'Waterproof': ["mv", "v"]}, title: "New Waterproof Document", defaultUri}).then((uri) => {
            if (!uri) {
                window.showErrorMessage("Something went wrong in creating a new waterproof document");
                return;
            }
            const newFilePath = Uri.joinPath(this.context.extensionUri, "misc-includes", "empty_waterproof_document.mv");
            workspace.fs.readFile(newFilePath)
                .then((data) => {
                    workspace.fs.writeFile(uri, data).then(() => {
                        // Open the file using the waterproof editor
                        // TODO: Hardcoded `coqEditor.coqEditor`.
                        commands.executeCommand("vscode.openWith", uri, "coqEditor.coqEditor");
                    });                    
                }, (err) => {
                    window.showErrorMessage("Could not create a new Waterproof file.");
                    console.error(`Could not read Waterproof tutorial file: ${err}`);
                    return;                   
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
    private registerCommand(name: string, handler: (...args: unknown[]) => void, editorCommand: boolean = false) {
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
            const replacement = `<input-area>\n\`\`\`coq\n\n\`\`\`\n</input-area>`;
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
        wpl.log("Start of initializeClient");
        
        // Whether the user has decided to skip the launch checks
        const launchChecksDisabled = WaterproofConfigHelper.skipLaunchChecks;

        if (launchChecksDisabled || this._isWeb) {
            const reason = launchChecksDisabled ? "Launch checks disabled by user." : "Web extension, skipping launch checks.";
            wpl.log(`${reason} Attempting to launch client...`);
        } else {
            // Run the version checker.
            const requiredCoqLSPVersion = this.context.extension.packageJSON.requiredCoqLspVersion;
            const requiredCoqWaterproofVersion = this.context.extension.packageJSON.requiredCoqWaterproofVersion;
            const versionChecker = new VersionChecker(WaterproofConfigHelper.configuration, this.context, requiredCoqLSPVersion, requiredCoqWaterproofVersion);
            
            // Check whether we can find coq-lsp
            const foundServer = await versionChecker.prelaunchChecks();
            if (foundServer) {
                // Only run the version checker after we know that there is a valid coq-lsp server
                versionChecker.run();
            } else {
                this.statusBar.failed("LSP not found");
            }
        }

        if (this.client?.isRunning()) {
            return Promise.reject(new Error("Cannot initialize client; one is already running."))
        }

        const serverOptions = CoqLspServerConfig.create(
            // TODO: Support +coqversion versions.
            this.context.extension.packageJSON.requiredCoqLspVersion.slice(2),
            WaterproofConfigHelper.configuration
        );

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "coqmarkdown" }, { language: "coq" }],  // both .mv and .v files
            outputChannelName: "Waterproof LSP Events (Initial)",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: serverOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        wpl.log("Initializing client...");
        this.client = this.clientFactory(this.context, clientOptions, WaterproofConfigHelper.configuration);
        return this.client.startWithHandlers(this.webviewManager).then(
            () => {
                // show user that LSP is working
                this.statusBar.update(true);
                this.clientRunning = true;
                wpl.log("Client initialization complete.");
            },
            reason => {
                const message = reason.toString();
                wpl.log(`Error during client initialization: ${message}`);
                this.statusBar.failed(message);
                throw reason;  // keep chain rejected
            }
        );
        
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
            this.clientRunning = false;
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
