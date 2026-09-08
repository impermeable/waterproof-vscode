import { Disposable } from "vscode";
import { CompositeClient } from "../../lsp-client/composite";

/**
 * This defines the interface of components that display
 * goal and message related information.
 *
 * This lives next to its implementations rather than in `src/components.ts`,
 * because it names the `CompositeClient`: the lsp-client layer imports the
 * component interfaces from there, so declaring it in that module would make
 * `components` and `lsp-client` mutually dependent.
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
