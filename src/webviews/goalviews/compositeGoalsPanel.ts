import { CompositeClient } from "../../lsp-client/composite";
import { GoalsPanel } from "./goalsPanel";
import { IGoalsComponent } from "../../components";
import { LeanLspClient } from "../../lsp-client/lean";
import { InfoProvider } from "../../infoview";
import { Location } from "vscode-languageserver-types";
import { WebviewEvents, WebviewState } from "../coqWebview";

export class CompositeGoalsPanel implements IGoalsComponent {
    protected lastClient?: CompositeClient;

    protected lastState?: 'goals' | 'infoview';
    protected infoProvider?: InfoProvider;

    constructor(
        protected readonly panel: GoalsPanel
    ) {
        panel.on(WebviewEvents.change, () => {
            if (panel.state === WebviewState.closed) {
                this.lastState = undefined;
            } else if (panel.state === WebviewState.visible) {
                this.updateGoals(this.lastClient!);
            }
        });
    }

    async updateGoals(client: CompositeClient): Promise<void> {
        if (!this.panel.isOpened) return;

        this.lastClient = client;

        if (client.activeClient instanceof LeanLspClient) {
            if (this.lastState !== 'infoview') {
                this.lastState = 'infoview';
                this.panel.showView("infoview");
                this.infoProvider?.resetServerState();
            }
            const loc: Location = {
                // FIXME: will we always have an active document here?
                uri: client.activeDocument!.uri.toString(),
                range: {
                    start: client.activeCursorPosition || { line: 0, character: 0 },
                    end: client.activeCursorPosition || { line: 0, character: 0 },
                },
            };
            try {
                // make sure we have an InfoView provider, update it
                if (this.infoProvider === undefined) {
                    this.infoProvider = new InfoProvider(client.activeClient, this.panel);
                    this.infoProvider.initInfoview(loc);
                } else {
                    this.infoProvider.sendPosition(loc);
                }
            } catch (e) {
                this.panel.showView("goals");
                this.lastState = 'goals';
                this.panel.failedGoals(e);
            }
        } else {
            if (this.lastState !== 'goals') {
                this.lastState = 'goals';
                this.panel.showView("goals");
            }
            return this.panel.updateGoals(client.activeClient);
        }
    }

    failedGoals(e: unknown): void {
        this.panel.failedGoals(e);
    }

    disable(): void {
        this.panel.disable();
    }

    dispose() {
        this.panel.dispose();
        this.infoProvider?.dispose();
    }
}
