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
import { WaterproofConfigHelper, WaterproofSetting, WaterproofLogger as wpl } from "./helpers";


import { convertToString } from "../lib/types";
import { Hypothesis } from "./api";

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
                for (const g of this.goalsComponents) g.updateGoals(undefined);

            }

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
        const goalsPanel = new GoalsPanel(this.context.extensionUri, CoqLspClientConfig.create())
        this.goalsComponents.push(goalsPanel);
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.webviewManager.open("goals");
        this.webviewManager.addToolWebview("symbols", new SymbolsPanel(this.context.extensionUri));
        this.webviewManager.addToolWebview("search", new Search(this.context.extensionUri));
        this.webviewManager.addToolWebview("help", new Help(this.context.extensionUri));
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.webviewManager.addToolWebview("tactics", new TacticsPanel(this.context.extensionUri));
        const debug = new DebugPanel(this.context.extensionUri, CoqLspClientConfig.create());
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
                case "win32": defaultValue = "C:\\waterproof_dependencies\\opam\\wp-3.0.0+9.0\\bin\\coq-lsp.exe"; break;
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

        this.registerCommand("autoInstall", async () => {
            commands.executeCommand(`waterproof.defaultPath`);

            const windowsInstallationScript = `echo Begin Waterproof dependency software installation && echo Downloading installer ... && curl -o Waterproof_Installer.exe -L https://github.com/impermeable/waterproof-dependencies-installer/releases/download/v3.0.0%2B9.0/Waterproof-dependencies-wp-3.0.0+9.0-Windows-x86_64.exe && echo Installer Finished Downloading - Please wait for the Installer to execute, this can take up to a few minutes && Waterproof_Installer.exe && echo Required Files Installed && del Waterproof_Installer.exe && echo COMPLETE - The Waterproof checker will restart automatically a few seconds after this terminal is closed`
            // TODO: this may need to be determined in a better way
            const uninstallerLocation = `C:\\waterproof_dependencies\\opam\\wp-3.0.0+9.0\\Uninstall.exe`

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
     * Request the goals for the current document and cursor position. 
     */
    public async goals(): Promise<{currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[]}> {
        if (!this.client.activeDocument || !this.client.activeCursorPosition) { throw new Error("No active document or cursor position."); }
        
        const document = this.client.activeDocument;
        const position = this.client.activeCursorPosition;

        const params = this.client.createGoalsRequestParameters(document, position);
        const goalResponse = await this.client.requestGoals(params);

        if (goalResponse.goals === undefined) {
            throw new Error("Response contained no goals.");
        }
    
        // Convert goals and hypotheses to strings
        const goalsAsStrings = goalResponse.goals.goals.map(g => convertToString(g.ty));
        // Note: only taking hypotheses from the first goal
        const hyps = goalResponse.goals.goals[0].hyps.map(h => { return {name: convertToString(h.names[0]), content: convertToString(h.ty)}; });

        return {currentGoal: goalsAsStrings[0], hypotheses: hyps, otherGoals: goalsAsStrings.slice(1)};
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
        const wpHelpResponse = await executeCommandFullOutput(this.client, "Help.");
        // Return the help messages. val[0] contains the levels, which we ignore.
        return wpHelpResponse.feedback.map(val => val[1]);
    }

    /**
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
    public proofContext(cursorMarker: string = "{!* CURSOR *!}"): {
        name: string,
        full: string
        withCursorMarker: string
    } {
        if (!this.client.activeDocument || !this.client.activeCursorPosition) {
            throw new Error("No active document or cursor position.");
        }

        const document = this.client.activeDocument;
        const position = this.client.activeCursorPosition;

        const pos = document.offsetAt(position);

        // This regex is used to find the statement the user is trying to proof.
        // see: https://rocq-prover.org/doc/V9.0.0/refman/language/core/definitions.html#assertions-and-proofs
        // We match for one of the `thm_token` followed by `ident_decl` (of which we ignore the universe part (univ_decl))
        // up to one of {Qed, Admitted, Defined} followed by a dot.
        // Note that the ident is allowed to contain unicode so this regex operators with the unicode flag enabled (/u).
        // \p{L} matches all the unicode symbols in the 'letter' category: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Regular_expressions/Unicode_character_class_escape
        const regex = /(?:Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property)\s+([A-Za-z_\p{L}][A-Za-z0-9_\p{L}']*)\s+[^]*?(?:Qed|Admitted|Defined)\./gu;
        const theProof = document.getText().matchAll(regex).find(v => {
            const start = v.index;
            const end = start + v[0].length;

            return (pos >= start && pos <= end);
        });

        if (theProof === undefined) {
            throw new Error("[proofContext] Could not find the proof the user is working on");
        }

        // Helper function to remove input-area tags, coq markers and extra whitespace from input string
        const removeMarkersAndWhitespace = (input: string) => {
            return input.replace(/<input-area>\s*```coq\s*/g, "")
                .replace(/\s*```\s*<\/input-area>/g, "")
                .replace(/```coq/g, "")
                .replace(/```/g, "")
                .replace(/\s+/g, " ");
        }

        const offsetIntoMatch = pos - theProof.index;
        const text = theProof[0];

        return {
            full: removeMarkersAndWhitespace(text),
            withCursorMarker: removeMarkersAndWhitespace(text.substring(0, offsetIntoMatch) + cursorMarker + text.substring(offsetIntoMatch)),
            name: theProof[1]
        }
    }

    /**
     * Try a proof/step by executing the given commands/tactics.
     * @param steps The proof steps to try. This can be a single tactic or command or multiple separated by the
     * usual `.` and space.
     */
    public async tryProof(steps: string): Promise<{finished: boolean, remainingGoals: string[]}> {
        const execResponse = await executeCommandFullOutput(this.client, steps);
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
            const requiredCoqLSPVersion = this.context.extension.packageJSON.requiredCoqLspVersion;
            const requiredCoqWaterproofVersion = this.context.extension.packageJSON.requiredCoqWaterproofVersion;
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

        const serverOptions = CoqLspServerConfig.create(
            // TODO: Support +coqversion versions.
            this.context.extension.packageJSON.requiredCoqLspVersion.slice(2)
        );

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "markdown" }, { language: "coq" }],  // both .mv and .v files
            outputChannelName: "Waterproof LSP Events (Initial)",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: serverOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        wpl.log("Initializing client...");
        this.client = this.clientFactory(this.context, clientOptions, WaterproofConfigHelper.configuration);
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
        wpl.debug(`Updating goals for document: ${document.uri.toString()} at position: ${position.line}:${position.character}`);
        if (!this.client.isRunning()) {
            wpl.debug("Client is not running, cannot update goals.");
            return;
        }
        const params = this.client.createGoalsRequestParameters(document, position);
        wpl.debug(`Requesting goals for components: ${this.goalsComponents}`);
        this.client.requestGoals(params).then(
            response => {
                wpl.debug(`Received goals response: ${JSON.stringify(response)}`);
                for (const g of this.goalsComponents) {
                    wpl.debug(`Updating goals component: ${g.constructor.name}`);
                    g.updateGoals(response)
                }
            },
            reason => {
                wpl.debug(`Failed for reason: ${reason}`);
                for (const g of this.goalsComponents) {
                    wpl.debug(`Failed to update goals component: ${g.constructor.name}`);
                    g.failedGoals(reason);
                }
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
