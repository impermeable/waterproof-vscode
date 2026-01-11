import {
    Disposable,
    ExtensionContext,
    Position,
    TextDocument,
    commands,
    workspace,
    window,
    ConfigurationTarget,
    Uri,
    TerminalShellExecutionCommandLineConfidence
} from "vscode";
import { LanguageClientOptions, RevealOutputChannelOn } from "vscode-languageclient";

import { IExecutor, IGoalsComponent, IStatusComponent } from "./components";
import { CoqnitiveStatusBar } from "./components/enableButton";
import { LanguageClientProviderFactory, LspClientConfig } from "./lsp-client/clientTypes";
import { CoqLspServerConfig } from "./lsp-client/coq";
import { LeanLspClient, LeanLspServerConfig } from "./lsp-client/lean";
import { executeCommand, executeCommandFullOutput } from "./lsp-client/commandExecutor";
import { CoqEditorProvider } from "./pm-editor";
import { checkConflictingExtensions, excludeCoqFileTypes } from "./util";
import { WebviewManager, WebviewManagerEvents } from "./webviewManager";
import { DebugPanel } from "./webviews/goalviews/debug";
import { GoalsPanel } from "./webviews/goalviews/goalsPanel";
import { SidePanelProvider, addSidePanel } from "./webviews/sidePanel";
import { Search } from "./webviews/standardviews/search";
import { Help } from "./webviews/standardviews/help";
import { ExecutePanel } from "./webviews/standardviews/execute";
import { SymbolsPanel } from "./webviews/standardviews/symbols";
import { TacticsPanel } from "./webviews/standardviews/tactics";

import { VersionChecker } from "./version-checker";
import { Utils } from "vscode-uri";
import { WaterproofConfigHelper, WaterproofFileUtil, WaterproofPackageJSON, WaterproofSetting, WaterproofLogger as wpl } from "./helpers";

import { convertToString } from "../lib/types";
import { Hypothesis } from "./api";
import { CompositeClient } from "./lsp-client/composite";
import { CompositeGoalsPanel } from "./webviews/goalviews/compositeGoalsPanel";
import { MessageType } from "../shared/Messages";

/**
 * Main extension class
 */
export class Waterproof implements Disposable {

    /** The extension context */
    private readonly context: ExtensionContext;

    /** The resources that must be released when this extension is disposed of */
    private readonly disposables: Disposable[] = [];

    /** The function that can create a new Coq language client provider */
    private readonly getCoqClientProvider: LanguageClientProviderFactory;

    /** The function that can create a new Lean language client provider */
    private readonly getLeanClientProvider: LanguageClientProviderFactory;

    /** The manager for (communication between) webviews */
    public readonly webviewManager: WebviewManager;

    /**
     * The client that communicates with the LSP server.
     * It's created by the `initializeClient` function.
     */
    public client!: CompositeClient;

    /** The status bar item that indicates whether this extension is running */
    private readonly statusBar: IStatusComponent;

    /** The components that display or process the goals and messages on the current line */
    private readonly goalsComponents: IGoalsComponent[] = [];

    /** The tactics panel */
    private readonly tacticsPanel: TacticsPanel;

    /** Main executor that allows for arbitrary execution */
    public readonly executorComponent: IExecutor;

    private sidePanelProvider: SidePanelProvider;

    private clientRunning: boolean = false;

    /**
     * Constructs the extension lifecycle object.
     *
     * @param context the extension context object
     */
    constructor(
        context: ExtensionContext,
        getCoqClientProvider: LanguageClientProviderFactory,
        getLeanClientProvider: LanguageClientProviderFactory,
        private readonly _isWeb = false
    ) {
        wpl.log("Waterproof initialized");
        checkConflictingExtensions();
        excludeCoqFileTypes();

        this.context = context;
        this.getCoqClientProvider = getCoqClientProvider;
        this.getLeanClientProvider = getLeanClientProvider;

        this.webviewManager = new WebviewManager();
        this.webviewManager.on(WebviewManagerEvents.editorReady, (document: TextDocument) => {
            this.client.updateCompletions(document);
        });
        this.webviewManager.on(WebviewManagerEvents.viewportHint, ({document, start, end}) => {
            this.client.sendViewportHint(document, start, end);
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
                this.webviewManager.open("goals");
                for (const g of this.goalsComponents) g.updateGoals(this.client);
            }

            this.tacticsPanel.update(this.client);
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
                executeCommand(this.client.coqClient, command).then(
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
        const goalsPanel = new GoalsPanel(this.context.extensionUri, LspClientConfig.create())
        const compositeGoalsPanel = new CompositeGoalsPanel(this.client, goalsPanel);
        this.goalsComponents.push(compositeGoalsPanel);
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.webviewManager.open("goals");
        this.webviewManager.addToolWebview("symbols", new SymbolsPanel(this.context.extensionUri));
        this.webviewManager.addToolWebview("search", new Search(this.context.extensionUri));
        this.webviewManager.addToolWebview("help", new Help(this.context.extensionUri));
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.tacticsPanel = new TacticsPanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("tactics", this.tacticsPanel);
        const debug = new DebugPanel(this.context.extensionUri, LspClientConfig.create());
        this.webviewManager.addToolWebview("debug", debug);
        this.goalsComponents.push(debug);

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
                case "darwin": defaultValue = "coq-lsp"; break;
                case "freebsd": defaultValue = undefined; break;
                case "haiku": defaultValue = undefined; break;
                // LINUX
                case "linux": defaultValue = "coq-lsp"; break;
                case "openbsd": defaultValue = undefined; break;
                case "sunos": defaultValue = undefined; break;
                // WINDOWS
                case "win32": defaultValue = WaterproofPackageJSON.defaultCoqLspPathWindows(this.context); break;
                case "cygwin": defaultValue = undefined; break;
                case "netbsd": defaultValue = undefined; break;
            }
            if (defaultValue === undefined) {
                window.showInformationMessage("Waterproof has no known default value for this platform, please update the setting manually.");
                commands.executeCommand("workbench.action.openSettings", "waterproof.path");
            } else {
                try {
                    WaterproofConfigHelper.update(WaterproofSetting.Path, defaultValue, ConfigurationTarget.Global).then(() => {
                        setTimeout(() => {
                            wpl.log("Waterproof Args setting changed to: " + WaterproofConfigHelper.get(WaterproofSetting.Path).toString());
                            window.showInformationMessage(`Waterproof Path setting succesfully updated!`);
                        }, 100);
                    });
                } catch (e) {
                    console.error("Error in updating Waterproof.path setting:", e);
                }
            }
        });

        this.registerCommand("setArgsWindowsBasedOnCoqLspPath", () => {
            const coqLspPath = WaterproofConfigHelper.get(WaterproofSetting.Path);
            if (coqLspPath !== "coq-lsp") {
                const coqlib = WaterproofFileUtil.join(WaterproofFileUtil.getDirectory(coqLspPath), "..\\lib\\coq");
                const findlib_config = WaterproofFileUtil.join(WaterproofFileUtil.getDirectory(coqLspPath), "findlib.conf");
                WaterproofConfigHelper.update(WaterproofSetting.Args, [`--coqlib=${coqlib}`, `--findlib_config=${findlib_config}`], ConfigurationTarget.Global);
            }
        });

        this.registerCommand("autoInstall", async () => {
            commands.executeCommand(`waterproof.defaultPath`);

            const downloadLink = WaterproofPackageJSON.installerDownloadLinkWindows(this.context);

            const windowsInstallationScript = `echo Begin Waterproof dependency software installation && echo Downloading installer ... && curl -o Waterproof_Installer.exe -L ${downloadLink} && echo Installer Finished Downloading - Please wait for the Installer to execute, this can take up to a few minutes && Waterproof_Installer.exe && echo Required Files Installed && del Waterproof_Installer.exe && echo COMPLETE - The Waterproof checker will restart automatically a few seconds after this terminal is closed`

            // default location of the uninstaller
            const uninstallerLocation =
                WaterproofFileUtil.join(
                    WaterproofFileUtil.getDirectory(WaterproofPackageJSON.defaultCoqLspPathWindows(this.context)),
                    `Uninstall.exe`);

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
            const updated = !WaterproofConfigHelper.get(WaterproofSetting.ShowLineNumbersInEditor);
            WaterproofConfigHelper.update(WaterproofSetting.ShowLineNumbersInEditor, updated);
            window.showInformationMessage(`Waterproof: Line numbers in editor are now ${updated ? "shown" : "hidden"}.`);
        });
    }

    /**
     * Get the currently active document in the editor.
     */
    public currentDocument(): TextDocument {
        if (!this.client.activeDocument) { throw new Error("No active document."); }
        return this.client.activeDocument;
    }

    /**
     * Executes the Help command at the cursor position and returns the output.
     */
    public async help(): Promise<Array<string>> {
        // Execute command
        const wpHelpResponse = await executeCommandFullOutput(this.client.coqClient, "Help.");
        // Return the help messages. val[0] contains the levels, which we ignore.
        return wpHelpResponse.feedback.map(val => val[1]);
    }

    /*,.*
     * Returns information about the current proof on a document level.
     * This function will look at the current document to figure out what
     * statement the user is currently proving.
     * @param cursorMarker The marker string to insert to indicate where the user has placed there
     * cursor in the current proof.
     * @returns An object containing:
     * - `name`: The name of the provable statement.
     * - `full`: The full statement that the user is working on from Theorem, Lemma, etc to Qed.
     * - `withCursorMarker`: The same as `full` but contains the {@linkcode cursorMarker} at the point where
     * the user has placed the cursor.
     */
    public async proofContext(cursorMarker: string = "{!* CURSOR *!}"): Promise<{
        name: string,
        full: string
        withCursorMarker: string
    }> {
        if (!this.client.activeDocument || !this.client.activeCursorPosition) {
            throw new Error("No active document or cursor position.");
        }

        const document = this.client.activeDocument;
        const position = this.client.activeCursorPosition;
        const posAsOffset = document.offsetAt(position);

        // Regex to find the end of the proof the user is working on.
        const endRegex = /(?:Qed|Admitted|Defined)\.\s/;
        // We request the document symbols with the goal of finding the lemma the user is working on.
        const symbols = await this.client.requestSymbols();
        const firstBefore = symbols.filter(s => {
            const sPos = new Position(s.range.start.line, s.range.start.character);
            return sPos.isBefore(position);
        }).at(-1);

        if (firstBefore === undefined) {
            throw new Error("Could not find lemma before cursor.");
        }
        // Compute the offset into the document where the proof starts (will be the position before Lemma)
        const startProof = document.offsetAt(new Position(firstBefore.range.start.line, firstBefore.range.start.character));

        // Get the part of the text of the document starting at the lemma statement.
        const docText = document.getText().substring(startProof);
        const proofClose = docText.match(endRegex);

        if (proofClose === null) {
            throw new Error("Could not find end of proof.");
        }

        // Get the text of the proof from the document, we need to add startProof to the index since the regex was run on a su
        const theProof = docText.substring(0, proofClose.index! + proofClose[0].length);

        // Helper function to remove input-area tags, coq markers and extra whitespace from input string
        const removeMarkersAndWhitespace = (input: string) => {
            return input.replace(/<input-area>\s*```coq\s*/g, "")
                .replace(/\s*```\s*<\/input-area>/g, "")
                .replace(/```coq/g, "")
                .replace(/```/g, "")
                .replace(/\s+/g, " ");
        }

        const offsetIntoMatch = posAsOffset - startProof;

        return {
            full: removeMarkersAndWhitespace(theProof),
            withCursorMarker: removeMarkersAndWhitespace(theProof.substring(0, offsetIntoMatch) + cursorMarker + theProof.substring(offsetIntoMatch)),
            name: firstBefore.name
        }
    }

    /**
     * Try a proof/step by executing the given commands/tactics.
     * @param steps The proof steps to try. This can be a single tactic or command or multiple separated by the
     * usual `.` and space.
     */
    public async tryProof(steps: string): Promise<{finished: boolean, remainingGoals: string[]}> {
        const execResponse = await executeCommandFullOutput(this.client.coqClient, steps);
        return {
            finished: execResponse.proof_finished,
            remainingGoals: execResponse.goals.map(g => convertToString(g.ty))
        };
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

    private async waterproofTutorialCommand(): Promise<void> {
        const hasWorkspaceOpen = workspace.workspaceFolders !== undefined && workspace.workspaceFolders.length != 0;
        const defaultUri = hasWorkspaceOpen ? Utils.joinPath(workspace.workspaceFolders![0].uri, "waterproof_tutorial.mv") : Uri.parse("./waterproof_tutorial.mv");
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
                        commands.executeCommand("vscode.openWith", uri, "waterproofTue.waterproofEditor");
                    });
                }, (err) => {
                    window.showErrorMessage("Could not open Waterproof tutorial file.");
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
        const hasWorkspaceOpen = workspace.workspaceFolders !== undefined && workspace.workspaceFolders.length != 0;
        const defaultUri = hasWorkspaceOpen ? Utils.joinPath(workspace.workspaceFolders![0].uri, "new_waterproof_document.mv") : Uri.parse("./new_waterproof_document.mv");
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
                        commands.executeCommand("vscode.openWith", uri, "waterproofTue.waterproofEditor");
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
        const launchChecksDisabled = WaterproofConfigHelper.get(WaterproofSetting.SkipLaunchChecks);

        if (launchChecksDisabled || this._isWeb) {
            const reason = launchChecksDisabled ? "Launch checks disabled by user." : "Web extension, skipping launch checks.";
            wpl.log(`${reason} Attempting to launch client...`);
        } else {
            // Run the version checker.
            const requiredCoqLSPVersion = WaterproofPackageJSON.requiredCoqLspVersion(this.context);
            const requiredCoqWaterproofVersion =  WaterproofPackageJSON.requiredCoqWaterproofVersion(this.context);
            const versionChecker = new VersionChecker(this.context, requiredCoqLSPVersion, requiredCoqWaterproofVersion);

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

        const coqServerOptions = CoqLspServerConfig.create(
            // TODO: Support +coqversion versions.
            WaterproofPackageJSON.requiredCoqLspVersion(this.context).slice(2)
        );

        const coqClientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "markdown" }, { language: "coq" }],  // .mv and .v files
            outputChannelName: "Waterproof LSP Events (Initial)",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: coqServerOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        const leanServerOptions = LeanLspServerConfig.create();

        const leanClientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "lean4" }],
            outputChannelName: "Waterproof LSP Events (Initial)",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: leanServerOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        wpl.log("Initializing client...");
        this.client = new CompositeClient(
            this.getCoqClientProvider(this.context, coqClientOptions, WaterproofConfigHelper.configuration),
            this.getLeanClientProvider(this.context, leanClientOptions, WaterproofConfigHelper.configuration),
        );
        return this.client.startWithHandlers(this.webviewManager).then(
            () => {
                this.webviewManager.open("goals");
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
            await this.client.dispose(2000);
            this.clientRunning = false;
            this.statusBar.update(false);
        } else {
            return Promise.resolve();
        }
    }

    /**
     * Request the goals for the current document and cursor position.
     */
    public async goals(): Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}> {
        return this.client.goals();
    }

    /**
     * This function gets called on TextEditorSelectionChange events and it requests the goals
     * if needed
     */
    private async updateGoals(document: TextDocument, position: Position): Promise<void> {
        wpl.debug(`Updating goals for document: ${document.uri.toString()} at position: ${position.line}:${position.character}`);
        if (!this.client.isRunning()) {
            wpl.debug("Client is not running, cannot update goals.");
            return;
        }
        wpl.debug(`Requesting goals for components: ${this.goalsComponents}`);

        for (const g of this.goalsComponents) {
            // TODO: avoid requesting goals separately for each component?
            //       (e.g. by caching requestGoals in LspClient)
            g.updateGoals(this.client);
        }
    }

    dispose() {
        this.statusBar.dispose();
        this.stopClient();
        for (const d of this.disposables) {
            d.dispose();
        }
    }
}
