import { Uri } from "vscode";
import { GoalAnswer, PpString } from "../../../lib/types";
import { CoqLspClientConfig } from "../../lsp-client/clientTypes";
import { CoqGoalsPanel } from "./coqGoalsPanel";
import { Message } from "../../../shared";
import { Disposable } from "vscode-languageclient";
import { WebviewEvents } from "../coqWebview";

export type PanelMode = 'coq' | 'lean';

export class GoalsPanel extends CoqGoalsPanel {

    private currentMode: PanelMode = 'coq';

    constructor(extensionUri: Uri, config: CoqLspClientConfig) {
        super(extensionUri, config);
    }

    public setMode(mode: PanelMode) {
        if (this.currentMode === mode) {
            return;
        }
        this.currentMode = mode;
        this.updatePanelContent();
    }

    protected override create() {
        super.create();
        // If we are in Lean mode, we need to overwrite the default Coq HTML
        // that super.create() just set.
        if (this.currentMode === 'lean') {
            this.updatePanelContent();
        }
    }

    private updatePanelContent() {
        if (!this._panel) return;

        if (this.currentMode === 'lean') {
            // Lean content generation
            const distBase = this._panel.webview.asWebviewUri(
                Uri.joinPath(this.extensionUri, "node_modules", "@leanprover", "infoview", "dist")
            );
            // We use the infoview's script logic
            const scriptUri = this._panel.webview.asWebviewUri(
                Uri.joinPath(this.extensionUri, "out", "views", "infoview", "index.js")
            );
            const libPostfix = `.production.min.js`;
            
            this._panel.webview.html = `
            <!DOCTYPE html>
            <html>
            <head>
                <meta charset="UTF-8" />
                <meta http-equiv="Content-type" content="text/html;charset=utf-8">
                <title>Infoview</title>
                <link rel="stylesheet" href="${distBase}/index.css">
            </head>
            <body>
                <div id="root"></div>
                <script
                    data-importmap-leanprover-infoview="${distBase}/index${libPostfix}"
                    data-importmap-react="${distBase}/react${libPostfix}"
                    data-importmap-react-jsx-runtime="${distBase}/react-jsx-runtime${libPostfix}"
                    data-importmap-react-dom="${distBase}/react-dom${libPostfix}"
                    src="${scriptUri}"></script>
            </body>
            </html>`;

        } else {
            // Coq content generation
            const styleUri = this._panel.webview.asWebviewUri(
                Uri.joinPath(this.extensionUri, "out", "views", "goals", "index.css")
            );
            const scriptUri = this._panel.webview.asWebviewUri(
                Uri.joinPath(this.extensionUri, "out", "views", "goals", "index.js")
            );

            this._panel.webview.html = `
            <!DOCTYPE html>
            <html lang="en">
            <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <link rel="stylesheet" type="text/css" href="${styleUri}">
            <script src="${scriptUri}" type="module"></script>
            <title>Coq's info panel</title>
            </head>
            <body>
                <div id="root"></div>
            </body>
            </html>
            `;
            
            // Restore previous Coq goals if available
            if (this.previousGoal) {
                setTimeout(() => {
                    if (this.previousGoal) super.updateGoals(this.previousGoal);
                }, 100);
            }
        }
    }

    override updateGoals(goals: GoalAnswer<PpString> | undefined) {
        // We capture the goals for restoration purposes even if we are in Lean mode
        this.previousGoal = goals;
        
        // But we only send the visual update message if we are actively in Coq mode
        if (this.currentMode === 'coq') {
            super.updateGoals(goals);
        }
    }

    public onInfoviewMes(callback: (msg: any) => void): Disposable {
        const handler = (msg: any) => callback(msg);
        this.on(WebviewEvents.message, handler);
        return {
            dispose: () => this.removeListener(WebviewEvents.message, handler)
        };
    }
}