import {
    Disposable,
    ExtensionContext,
    Position,
    TextDocument,
    WorkspaceConfiguration,
    commands,
    workspace,
    window} from "vscode";
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

import { newFileContent } from "./constants";
import { VersionChecker } from "./version-checker";

/**
 * Main extension class
 */
export class Coqnitive implements Disposable {

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

    private get configuration(): WorkspaceConfiguration {
        return workspace.getConfiguration("waterproof");
    }

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
        var goalsPanel = new GoalsPanel(this.context.extensionUri, CoqLspClientConfig.create(this.configuration))
        this.goalsComponents.push(goalsPanel);
        this.webviewManager.addToolWebview("goals", goalsPanel);
        this.webviewManager.open("goals")
        this.webviewManager.addToolWebview("symbols", new SymbolsPanel(this.context.extensionUri));
        this.webviewManager.addToolWebview("commonExecute", new CommonExecute(this.context.extensionUri));
        const executorPanel = new ExecutePanel(this.context.extensionUri);
        this.webviewManager.addToolWebview("execute", executorPanel);
        this.webviewManager.addToolWebview("tactics", new TacticsPanel(this.context.extensionUri));
        var logbook = new Logbook(this.context.extensionUri, CoqLspClientConfig.create(this.configuration));
        this.webviewManager.addToolWebview("logbook", logbook);
        this.goalsComponents.push(logbook);
        var debug = new DebugPanel(this.context.extensionUri, CoqLspClientConfig.create(this.configuration));
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
    }

    /**
     * Handle the newWaterproofDocument command. 
     * This command can be either activated by the user via the 'command palette' 
     * or by using the File -> New File... option. 
     */
    private async newFileCommand(): Promise<void> {

        window.showSaveDialog({filters: {'Waterproof': ["mv", "v"]}, title: "New Waterproof Document"}).then((uri) => {
            if (!uri) {
                window.showErrorMessage("Something went wrong in creating a new waterproof document");
                return;
            }

            workspace.fs.writeFile(uri, Buffer.from(newFileContent)).then(() => {
                // Open the file using the waterproof editor
                // TODO: Hardcoded `coqEditor.coqEditor`.
                commands.executeCommand("vscode.openWith", uri, "coqEditor.coqEditor");
            });
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
        const versionChecker = new VersionChecker(this.configuration, this.context, requiredCoqLSPVersion, requiredCoqWaterproofVersion);
        // 
        await versionChecker.prelaunchChecks();
        versionChecker.run();
        
        if (this.client?.isRunning()) {
            return Promise.reject(new Error("Cannot initialize client; one is already running."))
        }

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ language: "coqmarkdown" }],  // only `.mv` files, not `.v`
            outputChannelName: "Waterproof LSP Events",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions: CoqLspServerConfig.create(
                this.context.extension.packageJSON.requiredCoqLspVersion.slice(2),
                this.configuration
            ),
            markdown: { isTrusted: true, supportHtml: true },
        };

        this.client = this.clientFactory(clientOptions, this.configuration);
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
        if (this.client.isRunning()) {
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
