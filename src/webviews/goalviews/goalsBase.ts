import { Uri } from "vscode";
import { RocqGoalAnswer, PpString } from "../../../lib/types";
import { MessageType } from "../../../shared";
import { IGoalsComponent } from "../../components";
import { LspClientConfig } from "../../lsp-client/clientTypes";
// Type-only: `components` and `lsp-client` import from each other.
import type { CompositeClient } from "../../lsp-client/composite";
import { WaterproofPanel } from "../waterproofPanel";
import { WaterproofConfigHelper, WaterproofSetting } from "../../helpers";
import { RocqLspClient } from "../../lsp-client/rocq";
import { WaterproofLogger as wpl } from "../../helpers";

//class for panels that need Goals objects from coq-lsp
export abstract class GoalsBase
  extends WaterproofPanel
  implements IGoalsComponent
{
  protected config: LspClientConfig;

  constructor(
    extensionUri: Uri,
    config: LspClientConfig,
    name: string,
    supportInsert: boolean = false,
  ) {
    super(extensionUri, name, supportInsert);
    this.config = config;
  }

  getGoals(client: RocqLspClient): Promise<RocqGoalAnswer<PpString>> {
    return client.requestGoals();
  }

  /**
   * Sends message for renderGoals.
   *
   * These panels render Rocq goals, so they accept either the Rocq client
   * directly (as `CompositeGoalsPanel` passes it) or the `CompositeClient` (as
   * the goals components registered on the extension are given), picking the
   * Rocq client off the latter. The composite itself has no `requestGoals`.
   */
  async updateGoals(client: RocqLspClient | CompositeClient): Promise<void> {
    const rocqClient = "rocqClient" in client ? client.rocqClient : client;
    let goals: RocqGoalAnswer<PpString>;
    try {
      goals = await this.getGoals(rocqClient);
    } catch (error) {
      wpl.debug(`Failed to retrieve goals: ${error}`);
      this.failedGoals(error);
      return;
    }
    if (goals) {
      const visibility = WaterproofConfigHelper.get(
        WaterproofSetting.VisibilityOfHypotheses,
      );
      this.postMessage({
        type: MessageType.renderGoals,
        body: { goals, visibility },
      });
    }
  }

  //sends message for errorGoals
  failedGoals(e: unknown) {
    // FIXME: The error `e` should have a proper type instead of `unknown`.
    //        See `updateGoals` in extension.ts, where this `failedGoals`
    //        is called as the result of a Promise rejection.
    this.postMessage({ type: MessageType.errorGoals, body: e });
  }

  //deactivates panel
  disable() {
    this.deactivatePanel();
  }
}
