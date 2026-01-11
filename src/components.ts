import { Disposable, Position } from "vscode";
import { CoqGoalAnswer, PpString } from "../lib/types";
import { FileProgressParams } from "./lsp-client/requestTypes";
import { ILspClient } from "./lsp-client/clientTypes";

/**
 * This defines the interface of a component that displays
 * the status of the underlying lsp client
 */
export interface IStatusComponent extends Disposable {
    /**
     * Update the status bar component to display current status
     * of client
     *
     * @param clientRunning indicates whether the client is running
     */
    update(clientRunning: boolean): void;

    /**
     * Update the status bar to indicate failure to start client
     *
     * @param emsg the error that resulted in failure to start
     */
    failed(emsg: string): void;
}

/**
 * This defines the interface of a component that displays
 * the status of the underlying lsp client
 */
export interface ILineNumberComponent extends Disposable {
    update(pos: Position): void;
}

/**
 * This defines the interface of a component that displays
 * the progress of coq checking a file
 */
export interface IFileProgressComponent extends Disposable {
    /**
     * Called when the LSP client receives a notification that part of the document has been
     * processed.
     */
    onProgress(params: FileProgressParams): void;
}

/**
 * This defines the interface of components that display
 * goal and message related information
 */
export interface IGoalsComponent extends Disposable {

    /**
     * Update the goals component with the latest goals answer
     * from the coq-lsp server
     *
     * @param goals the goal answer object received from coq-lsp
     */
    updateGoals(client: ILspClient): Promise<void>;

    /**
     * Update the status bar to indicate failure to start client
     *
     * @param e the error that resulted in failure to receive
     *          goal answer
     */
    failedGoals(e: unknown): void;

    /**
     * Disable the GoalsComponent
     */
    disable(): void;
}

/**
 * This defines the interface of components that execute commands
*/
export interface IExecutor {
    setResults(results: CoqGoalAnswer<PpString> | string[]): void;
}
