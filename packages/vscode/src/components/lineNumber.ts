import { Position, StatusBarAlignment, StatusBarItem, window } from "vscode";
import { ILineNumberComponent } from "../components";

/**
 * The class that manages the line/character status bar item.
 */
export class LineStatusBar implements ILineNumberComponent {

    /**
     * The underlying UI component that displays the line/character.
     */
    private readonly statusBarItem: StatusBarItem;

    /**
     * Initializes the status bar item (with initially no content).
     */
    constructor() {
        this.statusBarItem = window.createStatusBarItem(StatusBarAlignment.Right, 100);
        this.statusBarItem.text = "";
        this.statusBarItem.show();
    }

    /**
     * Sets the status bar item to the specified `position`.
     */
    update(position: Position) {
        this.statusBarItem.text = `Ln ${position.line + 1}, Col ${position.character + 1}`;
    }

    /**
     * Releases the UI resources.
     */
    dispose() {
        this.statusBarItem.dispose();
    }

}
