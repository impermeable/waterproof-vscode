import { Disposable, Position } from "vscode";
import { RocqGoalAnswer, PpString } from "../lib/types";
import { FileProgressParams } from "./lsp-client/requestTypes";
// Type-only: `components` and `lsp-client` import from each other.
import type { CompositeClient } from "./lsp-client/composite";

/**
 * This defines the interface of a component that displays
 * the status of the underlying lsp client
 */
export interface IStatusComponent extends Disposable {
  /**
   * Update the status bar component to display current status
   * of client
   *
   * @param clientsRunning indicates which clients are running
   */
  update(clientsRunning: string[]): void;

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
 * the progress of rocq checking a file
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
   * @param client the composite client to request the goals from. Components
   *               that can only render the goals of a single language server
   *               have to pick the relevant client off it themselves.
   */
  updateGoals(client: CompositeClient): Promise<void>;

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
  setResults(results: RocqGoalAnswer<PpString> | string[]): void;
}
