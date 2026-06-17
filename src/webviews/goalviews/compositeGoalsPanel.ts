import { CompositeClient } from "../../lsp-client/composite";
import { GoalsPanel } from "./goalsPanel";
import { IGoalsComponent } from "../../components";
import { LeanLspClient } from "../../lsp-client/lean";
import { InfoProvider } from "../../infoview";
import { Location } from "vscode-languageserver-types";
import { WebviewEvents, WebviewState } from "../waterproofPanel";
import { WaterproofLogger as wpl } from "../../helpers";

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
                if (this.lastClient) {
                    this.updateGoals(this.lastClient);
                }
            }
        });
    }

    async updateGoals(client: CompositeClient): Promise<void> {
        wpl.debug(`[compositeGoals] updateGoals called, panelOpen=${this.panel.isOpened}, clientExists=${!!client}`);
        if (!this.panel.isOpened) return;

        this.lastClient = client;

        if (client.activeClient instanceof LeanLspClient) {
            const cursorPos = client.activeCursorPosition;
            const cursorStr = cursorPos ? `${cursorPos.line}:${cursorPos.character}` : "undefined";
            wpl.debug(`[compositeGoals] Lean path, lastState=${this.lastState}, cursorPos=${cursorStr}, activeDoc=${client.activeDocument?.uri.toString().split('/').pop()}`);
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
                    wpl.debug(`[compositeGoals] creating new InfoProvider, initInfoview at ${JSON.stringify(loc.range.start)}`);
                    this.infoProvider = new InfoProvider(client.activeClient, this.panel);
                    this.infoProvider.initInfoview(loc);
                } else {
                    wpl.debug(`[compositeGoals] sendPosition at ${JSON.stringify(loc.range.start)}`);
                    this.infoProvider.sendPosition(loc);
                }
            } catch (e) {
                wpl.debug(`[compositeGoals] error: ${e}`);
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
