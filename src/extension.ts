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
} from "vscode";
import {
    LanguageClientOptions,
    RevealOutputChannelOn,
    Location
} from "vscode-languageclient";

import { IExecutor, IGoalsComponent, IStatusComponent } from "./components";
import { CoqnitiveStatusBar } from "./components/enableButton";
import {
    CoqLspClient,
    CoqLspClientConfig,
    CoqLspClientFactory,
    CoqLspServerConfig,
    LeanLspClientFactory,
} from "./lsp-client/clientTypes";
import { executeCommand, executeCommandFullOutput } from "./lsp-client/commandExecutor";
import { CoqEditorProvider } from "./pm-editor";
import { checkConflictingExtensions, excludeCoqFileTypes } from "./util";
import { WebviewManager, WebviewManagerEvents } from "./webviewManager";
import { DebugPanel } from "./webviews/goalviews/debug";
// CHANGED: Import the new GoalsPanel (multiplexer)
import { GoalsPanel } from "./webviews/goalviews/goalsPanel";
import { SidePanelProvider, addSidePanel } from "./webviews/sidePanel";
import { Search } from "./webviews/standardviews/search";
import { Help } from "./webviews/standardviews/help";
import { ExecutePanel } from "./webviews/standardviews/execute";
import { SymbolsPanel } from "./webviews/standardviews/symbols";
import { TacticsPanel } from "./webviews/standardviews/tactics";

import { VersionChecker } from "./version-checker";
import { Utils } from "vscode-uri";
import { WebviewEvents, WebviewState } from "./webviews/coqWebview";
import {
    WaterproofConfigHelper,
    WaterproofSetting,
    WaterproofLogger as wpl,
    WaterproofFileUtil,
    WaterproofPackageJSON
} from "./helpers";
import {
    activateLeanClient,
    deactivateLeanClient,
    getLeanInstance,
    isLeanClientRunning,
    LeanLspClient,
    restartLeanClient,
} from "./lsp-client/leanlspclient";
import { LspClientFactory } from "./mainNode";
import { convertToString } from "../lib/types";
import { Hypothesis } from "./api";
import { MessageType, Message } from "../shared/Messages"; // Added MessageType import
import { InfoProvider } from "./infoview";

export function activate(_context: ExtensionContext): void {

    commands.executeCommand(
        `workbench.action.openWalkthrough`,
        `waterproof-tue.waterproof#waterproof.setup`,
        false
    );
    const context = _context as unknown as ExtensionContext;
    activateLeanClient(context).catch((err) =>
        console.error("lean client activation failed:", err)
    );
    const disposableRestart = commands.registerCommand("lean.restart", () =>
        restartLeanClient(context)
    );
    context.subscriptions.push(disposableRestart);
}

export class Waterproof implements Disposable {
    private readonly context: ExtensionContext;
    private readonly disposables: Disposable[] = [];
    private readonly clientFactory: LspClientFactory;
    public readonly webviewManager: WebviewManager;
    public coqClient!: CoqLspClient;
    public leanClient!: LeanLspClient;
    public activeClient: string;
    private readonly statusBar: IStatusComponent;
    private readonly goalsComponents: IGoalsComponent[] = [];
    public readonly executorComponent: IExecutor;
    private sidePanelProvider: SidePanelProvider;
    private coqClientRunning: boolean = false;
    private leanClientRunning: boolean = false;
    private infoProvider?: InfoProvider;
    private goalsPanel?: GoalsPanel;

    constructor(
        context: ExtensionContext,
        clientFactory: LspClientFactory,
        private readonly _isWeb = false
    ) {
        wpl.log("Waterproof initialized");
        checkConflictingExtensions();
        excludeCoqFileTypes();

        this.context = context;
        this.clientFactory = clientFactory;
        this.activeClient = "none";
        this.webviewManager = new WebviewManager();

        this.statusBar = new CoqnitiveStatusBar();

        // CHANGED: Use the new GoalsPanel (Multiplexer)
        const goalsPanel = new GoalsPanel(
            this.context.extensionUri,
            CoqLspClientConfig.create()
        );
        this.goalsComponents.push(goalsPanel);

        // Register it as 'goals' so it replaces the standard goals panel
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.goalsPanel = goalsPanel;
        goalsPanel.on(WebviewEvents.change, () => {
            void this.handleGoalsPanelStateChange();
        });
        this.webviewManager.on(
            WebviewManagerEvents.editorReady,
            (document: TextDocument) => {
                if (document.languageId.startsWith("lean")) {
                    this.leanClient.updateCompletions(document);
                } else {
                    this.coqClient.updateCompletions(document);
                }
            }
        );
        this.webviewManager.on(
            WebviewManagerEvents.viewportHint,
            ({ document, start, end }) => {
                wpl.debug(`[EXTENSION] ViewportHint event received for ${document.uri.fsPath}: ${start}-${end}`);
                if (document.languageId.startsWith("lean")) {
                    if (!this.leanClient || !this.leanClient.isRunning()) {
                        wpl.debug("[EXTENSION] ViewportHint: Lean client not available, skipping");
                        return;
                    }
                    wpl.debug("[EXTENSION] ViewportHint: Calling leanClient.sendViewportHint");
                    this.leanClient.sendViewportHint(document, start, end);
                } else {
                    if (!this.coqClient || !this.coqClient.isRunning()) {
                        wpl.debug("[EXTENSION] ViewportHint: Coq client not available, skipping");
                        return;
                    }
                    wpl.debug("[EXTENSION] ViewportHint: Calling coqClient.sendViewportHint");
                    this.coqClient.sendViewportHint(document, start, end);
                }
            }
        );

        this.webviewManager.on(
            WebviewManagerEvents.focus,
            async (document: TextDocument) => {
                wpl.log("Focus event received");
                if (document.languageId.startsWith("lean")) {
                    // CHANGED: Switch mode to Lean
                    goalsPanel.setMode('lean');
                    
                    // Switch tactics panel to Lean mode (safely)
                    this.safePostMessage("tactics", { type: MessageType.setTacticsMode, body: "lean" });
                    
                    if (!this.leanClientRunning) {
                        console.warn(
                            "Focus event received before client is ready. Waiting..."
                        );
                        const waitForClient = async (): Promise<void> => {
                            return new Promise((resolve) => {
                                const interval = setInterval(() => {
                                    if (this.leanClientRunning) {
                                        clearInterval(interval);
                                        resolve();
                                    }
                                }, 100);
                            });
                        };
                        await waitForClient();
                        wpl.log("Lean Client ready. Proceeding with focus event.");
                    }
                    this.activeClient = "lean4";
                    if (
                        this.leanClient.activeDocument?.uri.toString() !== document.uri.toString() ||
                        !this.infoProvider?.isInitialized
                    ) {
                        this.leanClient.activeDocument = document;
                        this.leanClient.activeCursorPosition = undefined;
                        this.webviewManager.open("goals");
                        if (this.infoProvider) {
                            const loc: Location = {
                                uri: document.uri.toString(),
                                range: {
                                    start: {
                                        line: 0, character: 0
                                    },
                                    end: {
                                        line: 0, character: 0
                                    }
                                }
                            }

                            if (!this.infoProvider.isInitialized) {
                                await this.infoProvider.initInfoview(loc)
                            } else {
                                this.infoProvider.sendPosition(loc)
                            }
                        }
                        for (const g of this.goalsComponents) g.updateGoals(undefined);
                    }
                } else {
                    // CHANGED: Switch mode to Coq
                    goalsPanel.setMode('coq');
                    // Switch tactics panel to Coq mode (safely)
                    this.safePostMessage("tactics", { type: MessageType.setTacticsMode, body: "coq" });

                    if (!this.coqClientRunning) {
                        console.warn(
                            "Focus event received before client is ready. Waiting..."
                        );
                        const waitForClient = async (): Promise<void> => {
                            return new Promise((resolve) => {
                                const interval = setInterval(() => {
                                    if (this.coqClientRunning) {
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
                    this.activeClient = 'coq';
                    if (this.coqClient.activeDocument?.uri.toString() !== document.uri.toString()) {
                        this.coqClient.activeDocument = document;
                        this.coqClient.activeCursorPosition = undefined;
                        this.webviewManager.open("goals");
                        for (const g of this.goalsComponents) g.updateGoals(undefined);
                    }
                }
            });

        this.webviewManager.on(
            WebviewManagerEvents.cursorChange,
            async (document: TextDocument, position: Position) => {
                if (document.languageId.startsWith('lean')) {
                    this.leanClient.activeDocument = document;
                    this.leanClient.activeCursorPosition = position;
                    if (this.infoProvider) {
                        const loc: Location = {
                            uri: document.uri.toString(),
                            range: {
                                start: { line: position.line, character: position.character },
                                end: { line: position.line, character: position.character },
                            },
                        };
                        this.infoProvider?.sendPosition(loc);
                    }
                } else {
                    this.coqClient.activeDocument = document;
                    this.coqClient.activeCursorPosition = position;
                    this.updateGoalsCoq(document, position);
                }
            });

        this.webviewManager.on(
            WebviewManagerEvents.command,
            (source: IExecutor, command: string) => {
                if (command == "createHelp") {
                    source.setResults(["createHelp"]);
                } else {
                    if (this.activeClient.startsWith('lean')) {
                        // executeCommand(this.leanClient, command).then(
                        //     results => {
                        //         source.setResults(results);
                        //     },
                        //     (error: Error) => {
                        //         source.setResults(["Error: " + error.message]);
                        //     }
                        // );
                    } else {
                        executeCommand(this.coqClient, command).then(
                            results => {
                                source.setResults(results);
                            },
                            (error: Error) => {
                                source.setResults(["Error: " + error.message]);
                            }
                        );
                    }
                }
            });

        this.disposables.push(
            CoqEditorProvider.register(context, this.webviewManager)
        );

        this.webviewManager.addToolWebview(
            "symbols",
            new SymbolsPanel(this.context.extensionUri)
        );
        this.webviewManager.addToolWebview(
            "search",
            new Search(this.context.extensionUri)
        );
        this.webviewManager.addToolWebview(
            "help",
            new Help(this.context.extensionUri)
        );
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.webviewManager.addToolWebview(
            "tactics",
            new TacticsPanel(this.context.extensionUri)
        );
        const debug = new DebugPanel(
            this.context.extensionUri,
            CoqLspClientConfig.create()
        );
        this.webviewManager.addToolWebview("debug", debug);
        this.goalsComponents.push(debug);

        this.sidePanelProvider = addSidePanel(context, this.webviewManager);

        this.executorComponent = executorPanel;

        wpl.log("Calling initializeClient...");
        this.registerCommand("start", this.initializeClient);
        this.registerCommand("restart", this.restartClient);
        this.registerCommand("toggle", this.toggleClient);
        this.registerCommand("stop", this.stopClient);
        this.registerCommand("exportExerciseSheet", this.exportExerciseSheet);
        this.registerCommand("newWaterproofDocument", this.newFileCommand);
        this.registerCommand("openTutorial", this.waterproofTutorialCommand);

        this.registerCommand("pathSetting", () => {
            commands.executeCommand("workbench.action.openSettings", "waterproof.path");
        });
        this.registerCommand("argsSetting", () => {
            commands.executeCommand("workbench.action.openSettings", "waterproof.args");
        });

        this.registerCommand("defaultPath", () => {
            let defaultValue: string | undefined;
            switch (process.platform) {
                case "aix":
                    defaultValue = undefined;
                    break;
                case "android":
                    defaultValue = undefined;
                    break;
                // MACOS
                case "darwin":
                    defaultValue = "coq-lsp";
                    break;
                case "freebsd":
                    defaultValue = undefined;
                    break;
                case "haiku":
                    defaultValue = undefined;
                    break;
                // LINUX
                case "linux":
                    defaultValue = "coq-lsp";
                    break;
                case "openbsd":
                    defaultValue = undefined;
                    break;
                case "sunos":
                    defaultValue = undefined;
                    break;
                // WINDOWS
                case "win32":
                    defaultValue =
                        WaterproofPackageJSON.defaultCoqLspPathWindows(this.context);
                    break;
                case "cygwin":
                    defaultValue = undefined;
                    break;
                case "netbsd":
                    defaultValue = undefined;
                    break;
            }
            if (defaultValue === undefined) {
                window.showInformationMessage(
                    "Waterproof has no known default value for this platform, please update the setting manually."
                );
                commands.executeCommand(
                    "workbench.action.openSettings",
                    "waterproof.path"
                );
            } else {
                try {
                    WaterproofConfigHelper.update(
                        WaterproofSetting.Path,
                        defaultValue,
                        ConfigurationTarget.Global
                    ).then(() => {
                        setTimeout(() => {
                            wpl.log(
                                "Waterproof Args setting changed to: " +
                                WaterproofConfigHelper.get(WaterproofSetting.Path).toString()
                            );
                            window.showInformationMessage(
                                `Waterproof Path setting succesfully updated!`
                            );
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
                case "aix":
                    cmnd = undefined;
                    break;
                case "android":
                    cmnd = undefined;
                    break;
                // MACOS - This is currently not implemented, future task
                case "darwin":
                    cmnd = undefined;
                    break;
                case "freebsd":
                    cmnd = undefined;
                    break;
                case "haiku":
                    cmnd = undefined;
                    break;
                // LINUX - This is currently not implemented, issues when dealing with different distros and basic packages, installation is also easy enough
                case "linux":
                    cmnd = undefined;
                    break;
                case "openbsd":
                    cmnd = undefined;
                    break;
                case "sunos":
                    cmnd = undefined;
                    break;
                // WINDOWS
                case "win32":
                // If a waterproof installation is found in the default location it is first uninstalled.
                // The path is updated to the default location so if an installation is present in another directory it still will not be utilised
                // The installer is then downloaded, run and then removed.
                // eslint-disable-next-line no-fallthrough
                case "cygwin":
                    cmnd =
                        `start "WATERPROOF INSTALLER" cmd /k "IF EXIST ` +
                        uninstallerLocation +
                        ` (echo Uninstalling previous installation of Waterproof && ` +
                        uninstallerLocation +
                        ` && ` +
                        windowsInstallationScript +
                        ` ) ELSE (echo No previous installation found && ` +
                        windowsInstallationScript +
                        ` )"`;
                    break;
                case "netbsd":
                    cmnd = undefined;
                    break;
            }

            if (cmnd === undefined) {
                window.showInformationMessage(
                    "Waterproof has no automatic installation process for this platform, please refer to the walktrough page."
                );
            } else {
                await this.autoInstall(cmnd);
            }
        });

        this.registerCommand("toggleInEditorLineNumbers", () => {
            const updated = !WaterproofConfigHelper.get(WaterproofSetting.ShowLineNumbersInEditor);
            WaterproofConfigHelper.update(WaterproofSetting.ShowLineNumbersInEditor, updated);
            window.showInformationMessage(`Waterproof: Line numbers in editor are now ${updated ? "shown" : "hidden"}.`);
        });
    }
    
    /**
     * Safely posts a message to a webview. If the webview is not ready/open, it catches the error and ignores it.
     */
    private safePostMessage(view: string, message: Message) {
        try {
            this.webviewManager.postMessage(view, message);
        } catch (e) {
            // Ignore errors if the view is not yet ready or visible
        }
    }

    /**
     * Request the goals for the current document and cursor position.
     */
    public async goals(): Promise<{ currentGoal: string, hypotheses: Array<Hypothesis>, otherGoals: string[] }> {
        if (this.activeClient == "lean4") {
            if (!this.leanClient.activeDocument || !this.leanClient.activeCursorPosition) { throw new Error("No active document or cursor position."); }

            const document = this.leanClient.activeDocument;
            const position = this.leanClient.activeCursorPosition;

            const params = this.leanClient.createGoalsRequestParameters(document, position);
            const goalResponse = await this.leanClient.requestGoals(params);

            if (goalResponse.goals === undefined) {
                throw new Error("Response contained no goals.");
            }

            // Convert goals and hypotheses to strings
            const goalsAsStrings = goalResponse.goals.goals.map(g => convertToString(g.ty));
            // Note: only taking hypotheses from the first goal
            const hyps = goalResponse.goals.goals[0].hyps.map(h => { return { name: convertToString(h.names[0]), content: convertToString(h.ty) }; });


            return { currentGoal: goalsAsStrings[0], hypotheses: hyps, otherGoals: goalsAsStrings.slice(1) };
        } else {
            if (!this.coqClient.activeDocument || !this.coqClient.activeCursorPosition) { throw new Error("No active document or cursor position."); }

            const document = this.coqClient.activeDocument;
            const position = this.coqClient.activeCursorPosition;

            const params = this.coqClient.createGoalsRequestParameters(document, position);
            const goalResponse = await this.coqClient.requestGoals(params);

            if (goalResponse.goals === undefined) {
                throw new Error("Response contained no goals.");
            }

            // Convert goals and hypotheses to strings
            const goalsAsStrings = goalResponse.goals.goals.map(g => convertToString(g.ty));
            // Note: only taking hypotheses from the first goal
            const hyps = goalResponse.goals.goals[0].hyps.map(h => { return { name: convertToString(h.names[0]), content: convertToString(h.ty) }; });


            return { currentGoal: goalsAsStrings[0], hypotheses: hyps, otherGoals: goalsAsStrings.slice(1) };
        }
    }

    /**
     * Get the currently active document in the editor.
     */
    public currentDocument(): TextDocument {
        if (this.activeClient == "lean4") {
            if (!this.leanClient.activeDocument) { throw new Error("No active document."); }
            return this.leanClient.activeDocument;
        } else {
            if (!this.coqClient.activeDocument) { throw new Error("No active document."); }
            return this.coqClient.activeDocument;
        }
    }

    /**
     * Executes the Help command at the cursor position and returns the output.
     */
    public async help(): Promise<Array<string>> {
        // Execute command
        const wpHelpResponse = await executeCommandFullOutput(this.coqClient, "Help.");
        // Return the help messages. val[0] contains the levels, which we ignore.
        return wpHelpResponse.feedback.map(val => val[1]);
    }

    // TODO: add lean client to proofContext
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
    public async proofContext(cursorMarker: string = "{!* CURSOR *!}"): Promise<{
        name: string,
        full: string
        withCursorMarker: string
    }> {
        if (!this.coqClient.activeDocument || !this.coqClient.activeCursorPosition) {
            throw new Error("No active document or cursor position.");
        }

        const document = this.coqClient.activeDocument;
        const position = this.coqClient.activeCursorPosition;
        const posAsOffset = document.offsetAt(position);

        // Regex to find the end of the proof the user is working on.
        const endRegex = /(?:Qed|Admitted|Defined)\.\s/;
        // We request the document symbols with the goal of finding the lemma the user is working on.
        const symbols = await this.coqClient.requestSymbols();
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

    // TODO: add lean client
    /**
     * Try a proof/step by executing the given commands/tactics.
     * @param steps The proof steps to try. This can be a single tactic or command or multiple separated by the
     * usual `.` and space.
     */
    public async tryProof(steps: string): Promise<{ finished: boolean, remainingGoals: string[] }> {
        const execResponse = await executeCommandFullOutput(this.coqClient, steps);
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
            exec(command, (err: unknown, _stdout: unknown, _stderr: unknown) => {
                if (err) {
                    // Simple fixed scripts are run, the user is able to stop these but they are not considered errors
                    // as the user has freedom to choose the steps and can rerun the command.
                }
                this.initializeClient();
                resolve(true);
            });
        });
    }

    private async waterproofTutorialCommand(): Promise<void> {
        const hasWorkspaceOpen =
            workspace.workspaceFolders !== undefined &&
            workspace.workspaceFolders.length != 0;
        const defaultUri = hasWorkspaceOpen
            ? Utils.joinPath(
                workspace.workspaceFolders![0].uri,
                "waterproof_tutorial.mv"
            )
            : Uri.parse("./waterproof_tutorial.mv");
        window
            .showSaveDialog({
                filters: { Waterproof: ["mv", "v"] },
                title: "Waterproof Tutorial",
                defaultUri,
            })
            .then((uri) => {
                if (!uri) {
                    window.showErrorMessage(
                        "Something went wrong in saving the Waterproof tutorial file"
                    );
                    return;
                }
                const newFilePath = Uri.joinPath(
                    this.context.extensionUri,
                    "misc-includes",
                    "waterproof_tutorial.mv"
                );
                workspace.fs.readFile(newFilePath).then(
                    (data) => {
                        workspace.fs.writeFile(uri, data).then(() => {
                            commands.executeCommand(
                                "vscode.openWith",
                                uri,
                                "waterproofTue.waterproofEditor"
                            );
                        });
                    },
                    (err) => {
                        window.showErrorMessage("Could not open Waterproof tutorial file.");
                        console.error(`Could not read Waterproof tutorial file: ${err}`);
                        return;
                    }
                );
            });
    }

    private async newFileCommand(): Promise<void> {
        const hasWorkspaceOpen =
            workspace.workspaceFolders !== undefined &&
            workspace.workspaceFolders.length != 0;
        const defaultUri = hasWorkspaceOpen
            ? Utils.joinPath(
                workspace.workspaceFolders![0].uri,
                "new_waterproof_document.mv"
            )
            : Uri.parse("./new_waterproof_document.mv");
        window
            .showSaveDialog({
                filters: { Waterproof: ["mv", "v"] },
                title: "New Waterproof Document",
                defaultUri,
            })
            .then((uri) => {
                if (!uri) {
                    window.showErrorMessage(
                        "Something went wrong in creating a new waterproof document"
                    );
                    return;
                }
                const newFilePath = Uri.joinPath(
                    this.context.extensionUri,
                    "misc-includes",
                    "empty_waterproof_document.mv"
                );
                workspace.fs.readFile(newFilePath).then(
                    (data) => {
                        workspace.fs.writeFile(uri, data).then(() => {
                            commands.executeCommand(
                                "vscode.openWith",
                                uri,
                                "waterproofTue.waterproofEditor"
                            );
                        });
                    },
                    (err) => {
                        window.showErrorMessage("Could not create a new Waterproof file.");
                        console.error(`Could not read Waterproof tutorial file: ${err}`);
                        return;
                    }
                );
            });
    }

    private registerCommand(
        name: string,
        handler: (...args: unknown[]) => void,
        editorCommand: boolean = false
    ) {
        const register = editorCommand
            ? commands.registerTextEditorCommand
            : commands.registerCommand;
        this.disposables.push(register("waterproof." + name, handler, this));
    }

    async exportExerciseSheet() {
        const document = this.coqClient.activeDocument;
        if (document) {
            let content = document.getText();
            const pattern = /<input-area>\s*```coq([\s\S]*?)\s*```\s<\/input-area>/g;
            const replacement = `<input-area>\n\`\`\`coq\n\n\`\`\`\n</input-area>`;
            content = content.replace(pattern, replacement);
            const fileUri = await window.showSaveDialog();
            if (fileUri) {
                await workspace.fs.writeFile(fileUri, Buffer.from(content, "utf8"));
                window.showInformationMessage(`Saved to: ${fileUri.fsPath}`);
            }
        }
    }

    async initializeClient(): Promise<void> {
        wpl.log("Start of initializeClient");

        const launchChecksDisabled = WaterproofConfigHelper.get(
            WaterproofSetting.SkipLaunchChecks
        );

        if (launchChecksDisabled || this._isWeb) {
            const reason = launchChecksDisabled ? "Launch checks disabled by user." : "Web extension, skipping launch checks.";
            wpl.log(`${reason} Attempting to launch client...`);
        } else {
            // Run the version checker.
            const requiredCoqLSPVersion =
                WaterproofPackageJSON.requiredCoqLspVersion(this.context);
            const requiredCoqWaterproofVersion =
                WaterproofPackageJSON.requiredCoqWaterproofVersion(this.context);
            const versionChecker =
                new VersionChecker(this.context, requiredCoqLSPVersion, requiredCoqWaterproofVersion);

            // Check whether we can find coq-lsp
            const foundServer = await versionChecker.prelaunchChecks();
            if (foundServer) {
                // Only run the version checker after we know that there is a valid coq-lsp server
                versionChecker.run();
            } else {
                this.statusBar.failed("LSP not found");
            }
        }

        if (this.coqClient?.isRunning()) {
            return Promise.reject(
                new Error("Cannot initialize client; one is already running.")
            );
        }

        const serverOptions = CoqLspServerConfig.create(
            // TODO: Support +coqversion versions.
            WaterproofPackageJSON.requiredCoqLspVersion(this.context).slice(2)
        );

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "markdown" }, { language: "coq" }, { language: "lean4" }],  // .mv, .v, and .lean files
            outputChannelName: "Waterproof LSP Events (Initial)",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: serverOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        wpl.log("Initializing client...");
        this.coqClient = this.clientFactory(
            this.context,
            clientOptions,
            WaterproofConfigHelper.configuration
        );
        return this.coqClient.startWithHandlers(this.webviewManager).then(
            () => {
                this.webviewManager.open("goals");
                this.statusBar.update(true);
                this.coqClientRunning = true;
                wpl.log("Client initialization complete.");
            },
            (reason: any) => {
                const message = reason.toString();
                wpl.log(`Error during client initialization: ${message}`);
                this.statusBar.failed(message);
                throw reason;
            }
        );
    }

    async initializeLeanClient(): Promise<void> {
        wpl.log("Start of initializeLeanClient");

        if (this.leanClient?.isRunning && this.leanClient.isRunning()) {
            return Promise.reject(
                new Error("Cannot initialize Lean client; one is already running.")
            );
        }

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "lean4" }],
            outputChannelName: "Waterproof Lean LSP",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
        };

        wpl.log("Initializing Lean client via clientFactory...");
        this.leanClient = this.clientFactory(
            this.context,
            clientOptions,
            "lean"
        ) as LeanLspClient;

        return this.leanClient.startWithHandlers(this.webviewManager).then(
            () => {
                this.webviewManager.open("goals");
                this.statusBar.update(true);
                this.leanClientRunning = true;
                wpl.log("Lean client initialization complete.");

                this.infoProvider = new InfoProvider(this.leanClient);
                this.infoProvider.attachHost(this.goalsPanel);
            },
            (reason) => {
                const message = String(reason);
                wpl.log(`Error during Lean client initialization: ${message}`);
                this.statusBar.failed(message);
                throw reason;
            }
        );
    }

    private async handleGoalsPanelStateChange() {
        if (!this.goalsPanel || !this.infoProvider) {
            return;
        }

        if (this.goalsPanel.state === WebviewState.closed) {
            this.infoProvider.isInitialized = false;
            return;
        }

        if (this.goalsPanel.state !== WebviewState.visible) {
            return;
        }

        if (!this.leanClientRunning || this.activeClient !== "lean4") {
            return;
        }

        const doc = this.leanClient?.activeDocument ?? window.activeTextEditor?.document;
        if (!doc || !doc.languageId.startsWith("lean")) {
            return;
        }

        const position = this.leanClient.activeCursorPosition ?? new Position(0, 0);
        const loc: Location = {
            uri: doc.uri.toString(),
            range: {
                start: { line: position.line, character: position.character },
                end: { line: position.line, character: position.character },
            },
        };

        if (!this.infoProvider.isInitialized) {
            await this.infoProvider.initInfoview(loc);
        } else {
            await this.infoProvider.sendPosition(loc);
        }
    }


    /**
     * Restarts the Coq LSP client.
     */
    private async restartClient(): Promise<void> {
        await this.stopClient();
        await this.initializeClient();
    }

    private toggleClient(): Promise<void> {
        if (this.coqClient?.isRunning()) {
            return this.stopClient();
        } else {
            return this.initializeClient();
        }
    }

    private async stopClient(): Promise<void> {
        if (this.coqClient.isRunning()) {
            for (const g of this.goalsComponents) g.disable();
            await this.coqClient.dispose(2000);
            this.coqClientRunning = false;
            this.statusBar.update(false);
        } else {
            return Promise.resolve();
        }
    }

    private async updateGoalsCoq(
        document: TextDocument,
        position: Position
    ): Promise<void> {
        wpl.debug(
            `Updating goals for document: ${document.uri.toString()} at position: ${position.line
            }:${position.character}`
        );
        if (!this.coqClient.isRunning()) {
            wpl.debug("Client is not running, cannot update goals.");
            return;
        }
        const params = this.coqClient.createGoalsRequestParameters(
            document,
            position
        );
        wpl.debug(`Requesting goals for components: ${this.goalsComponents}`);
        this.coqClient.requestGoals(params).then(
            (response: any) => {
                wpl.debug(`Received goals response: ${JSON.stringify(response)}`);
                for (const g of this.goalsComponents) {
                    wpl.debug(`Updating goals component: ${g.constructor.name}`);
                    g.updateGoals(response);
                }
            },
            (reason: any) => {
                wpl.debug(`Failed for reason: ${reason}`);
                for (const g of this.goalsComponents) {
                    wpl.debug(`Failed to update goals component: ${g.constructor.name}`);
                    g.failedGoals(reason);
                }
            }
        );
    }

    private async updateGoalsLean(
        document: TextDocument,
        position: Position
    ): Promise<void> {
        wpl.debug("=== UPDATE GOALS LEAN ===");
        wpl.debug(`Document: ${document.uri.fsPath}`);
        wpl.debug(`Position: ${position.line}:${position.character}`);

        if (!this.leanClient) {
            wpl.debug("ERROR: leanClient is not initialized!");
            return;
        }

        if (!this.leanClient.isRunning()) {
            wpl.debug("ERROR: Lean client is not running!");
            return;
        }

        const params = this.leanClient.createGoalsRequestParameters(document, position);
        //wpl.debug(`Request params: ${JSON.stringify(params)}`);
        wpl.debug(`Number of goals components: ${this.goalsComponents.length}`);

        this.leanClient.requestGoals(params).then(
            (response) => {
                wpl.debug("=== GOALS RESPONSE RECEIVED ===");
                wpl.debug(`Response has goals?: ${response.goals ? "YES" : "NO"}`);
                if (response.goals) {
                    wpl.debug(`Goals config goals count: ${response.goals.goals?.length || 0}`);
                }
                //wpl.debug(`Full response: ${JSON.stringify(response, null, 2)}`);

                for (const g of this.goalsComponents) {
                    wpl.debug(`Updating goals component: ${g.constructor.name}`);
                    g.updateGoals(response);
                }
                wpl.debug("=== GOALS UPDATED ===");
            },
            (reason) => {
                wpl.debug(`ERROR: Failed to get goals - ${reason}`);
                for (const g of this.goalsComponents) {
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

export async function deactivate(): Promise<void> {
    await deactivateLeanClient();
    return;
}