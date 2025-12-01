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
import { executeCommand } from "./lsp-client/commandExecutor";
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
import {
  WaterproofConfigHelper,
  WaterproofSetting,
  WaterproofLogger as wpl,
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
        if (document.languageId.startsWith("lean")) {
          this.leanClient.sendViewportHint(document, start, end);
        } else {
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

          if (!isLeanClientRunning()) {
            console.warn(
              "Focus event received before client is ready. Waiting..."
            );
            const waitForClient = async (): Promise<void> => {
              return new Promise((resolve) => {
                const interval = setInterval(() => {
                  if (isLeanClientRunning()) {
                    clearInterval(interval);
                    resolve();
                  }
                }, 100);
              });
            };
            await waitForClient();
            wpl.log("Lean Client ready. Proceeding with focus event.");
          }
          this.leanClient = <LeanLspClient>getLeanInstance();
          this.activeClient = "lean4";
          
          if (
            this.leanClient.activeDocument?.uri.toString() !==
            document.uri.toString()
          ) {
            this.leanClient.activeDocument = document;
            this.leanClient.activeCursorPosition = undefined;
            this.webviewManager.open("goals");
            for (const g of this.goalsComponents) g.updateGoals(undefined);
          }
        } else {
          // CHANGED: Switch mode to Coq
          goalsPanel.setMode('coq');

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
      (document: TextDocument, position: Position) => {
        if (document.languageId.startsWith('lean')) {
          this.leanClient.activeDocument = document;
          this.leanClient.activeCursorPosition = position;
          this.updateGoalsLean(document, position);
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
            executeCommand(this.leanClient, command).then(
              results => {
                source.setResults(results);
              },
              (error: Error) => {
                source.setResults(["Error: " + error.message]);
              }
            );
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
            "C:\\waterproof_dependencies\\opam\\wp-3.0.0+9.0\\bin\\coq-lsp.exe";
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

    this.registerCommand("autoInstall", async () => {
      commands.executeCommand(`waterproof.defaultPath`);

      const windowsInstallationScript = `echo Begin Waterproof dependency software installation && echo Downloading installer ... && curl -o Waterproof_Installer.exe -L https://github.com/impermeable/waterproof-dependencies-installer/releases/download/v3.0.0%2B9.0/Waterproof-dependencies-wp-3.0.0+9.0-Windows-x86_64.exe && echo Installer Finished Downloading - Please wait for the Installer to execute, this can take up to a few minutes && Waterproof_Installer.exe && echo Required Files Installed && del Waterproof_Installer.exe && echo COMPLETE - The Waterproof checker will restart automatically a few seconds after this terminal is closed`;
      // TODO: this may need to be determined in a better way
      const uninstallerLocation = `C:\\waterproof_dependencies\\opam\\wp-3.0.0+9.0\\Uninstall.exe`;

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
      const updated = !WaterproofConfigHelper.get(
        WaterproofSetting.ShowLineNumbersInEditor
      );
      WaterproofConfigHelper.update(
        WaterproofSetting.ShowLineNumbersInEditor,
        updated
      );
      window.showInformationMessage(
        `Waterproof: Line numbers in editor are now ${updated ? "shown" : "hidden"
        }.`
      );
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
      const reason = launchChecksDisabled
        ? "Launch checks disabled by user."
        : "Web extension, skipping launch checks.";
      wpl.log(`${reason} Attempting to launch client...`);
    } else {
      const requiredCoqLSPVersion =
        this.context.extension.packageJSON.requiredCoqLspVersion;
      const requiredCoqWaterproofVersion =
        this.context.extension.packageJSON.requiredCoqWaterproofVersion;
      const versionChecker = new VersionChecker(
        this.context,
        requiredCoqLSPVersion,
        requiredCoqWaterproofVersion
      );

      const foundServer = await versionChecker.prelaunchChecks();
      if (foundServer) {
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
      this.context.extension.packageJSON.requiredCoqLspVersion.slice(2)
    );

    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ language: "rocqmarkdown" }, { language: "rocq" }],
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
    wpl.debug("Called update goals ");
    wpl.debug(
      `Updating goals for document: ${document.uri.toString()} at position: ${position.line
      }:${position.character}`
    );
    if (!this.leanClient.isRunning()) {
      wpl.debug("Client is not running, cannot update goals.");
      return;
    }
    const params = this.leanClient.createGoalsRequestParameters(
      document,
      position
    );
    wpl.debug(`Requesting goals for components: ${this.goalsComponents}`);
    this.leanClient.requestGoals(params).then(
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