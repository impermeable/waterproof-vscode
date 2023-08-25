import { MarkdownString, StatusBarAlignment, StatusBarItem, ThemeColor, window } from "vscode";
import { IStatusComponent } from "../components";

/**
 * A wrapper class that provides an interface to a vscode status
 * bar element displaying the lsp client status
 * @public
 */
export class CoqnitiveStatusBar implements IStatusComponent {
    // The status bar item this class wraps around
    private item: StatusBarItem;

    /**
     * Constructs the status bar item used to toggle the lsp client
     */
    constructor() {
        this.item = window.createStatusBarItem(
            "waterproof.enable",
            StatusBarAlignment.Left,
            0
        );
        this.item.command = "waterproof.toggle";
        this.item.text = "$(watch) Waterproof checker (starting...)";
        this.item.show();
    }

    update(clientRunning: boolean): void {
        if (clientRunning) {
            this.item.backgroundColor = undefined;
            this.item.text = "$(check) Waterproof checker";
            this.item.tooltip = "Waterproof document checker is running. Click to stop.";
        } else {
            this.item.backgroundColor = new ThemeColor("statusBarItem.warningBackground");
            this.item.text = "$(circle-slash) Waterproof checker (stopped)";
            this.item.tooltip = new MarkdownString("Waterproof document checker is *not* running. Click to start.");
        }
    }

    failed(emsg: string) {
        this.item.backgroundColor = new ThemeColor("statusBarItem.errorBackground");
        this.item.text = "$(circle-slash) Waterproof checker (failed to start)";
        this.item.tooltip = "Waterproof document checker failed to start. Click to retry.";
    }

    dispose(): void {
        this.item.dispose();
    }
}
