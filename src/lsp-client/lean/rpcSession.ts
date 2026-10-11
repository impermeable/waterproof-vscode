import { Disposable } from "vscode";
import type {
  RpcConnected,
  RpcConnectParams,
  RpcKeepAliveParams,
} from "@leanprover/infoview-api";
import type { LanguageClient } from "../clientTypes";

const KEEP_ALIVE_PERIOD_MS = 10000;

/**
 * An RPC session with the Lean server for one document. The server closes a session that is
 * not kept alive, so a keep-alive is sent periodically until the session is disposed.
 */
export class LeanRpcSession implements Disposable {
  private keepAlive?: ReturnType<typeof setInterval>;

  private constructor(
    client: LanguageClient,
    readonly uri: string,
    readonly sessionId: string,
    onLost?: (reason: unknown) => void,
  ) {
    this.keepAlive = setInterval(() => {
      const params: RpcKeepAliveParams = { uri, sessionId };
      client
        .sendNotification("$/lean/rpc/keepAlive", params)
        .catch((reason: unknown) => {
          this.dispose();
          onLost?.(reason);
        });
    }, KEEP_ALIVE_PERIOD_MS);
  }

  /**
   * Connects to the Lean server for the document `uri`.
   * @param onLost Called when a keep-alive could not be sent; the session is disposed by then.
   */
  static async connect(
    client: LanguageClient,
    uri: string,
    onLost?: (reason: unknown) => void,
  ): Promise<LeanRpcSession> {
    const params: RpcConnectParams = { uri };
    const { sessionId }: RpcConnected = await client.sendRequest(
      "$/lean/rpc/connect",
      params,
    );
    return new LeanRpcSession(client, uri, sessionId, onLost);
  }

  dispose() {
    clearInterval(this.keepAlive);
    this.keepAlive = undefined;
  }
}
