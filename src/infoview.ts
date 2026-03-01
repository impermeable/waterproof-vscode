import {
    EditorApi,
    InfoviewApi,
    InfoviewConfig,
    RpcConnected,
    RpcConnectParams,
    RpcKeepAliveParams,
    ServerStoppedReason,
} from '@leanprover/infoview-api'
import { Rpc } from './helpers/rpc';
import { MessageType } from '../shared';
import {
    ConfigurationTarget,
    Disposable,
    env,
    Position,
    workspace,
} from 'vscode'
import { LeanLspClient } from './lsp-client/lean';
import { DocumentUri, WorkspaceEdit, Location } from 'vscode-languageserver-protocol';
import { GoalsPanel } from './webviews/goalviews/goalsPanel';
import { WaterproofConfigHelper, WaterproofLogger as wpl, WaterproofSetting } from './helpers';
import { WebviewEvents } from './webviews/coqWebview';

const keepAlivePeriodMs = 10000

/**
 * Connects client to server and returns result
 */
async function rpcConnect(client: LeanLspClient, uri: DocumentUri): Promise<string> {
    const connParams: RpcConnectParams = { uri }
    try {
        const result: RpcConnected = await client.client.sendRequest('$/lean/rpc/connect', connParams)
        return result.sessionId
    } catch (e) {
        wpl.log(`Could not initialize a Lean RPC session: ${e}`)
        throw e;
    }
}

/**
 * The class for rpc session
 */
class RpcSessionAtPos implements Disposable {
    keepAliveInterval?: NodeJS.Timeout
    client: LeanLspClient

    constructor(
        client: LeanLspClient,
        public sessionId: string,
        public uri: DocumentUri,
    ) {
        this.client = client;
        this.keepAliveInterval = setInterval(async () => {
            const params: RpcKeepAliveParams = { uri, sessionId }
            try {
                await client.client.sendNotification('$/lean/rpc/keepAlive', params)
            } catch (e) {
                wpl.log(`[InfoProvider] failed to send keepalive for ${uri}: ${e}`)
                if (this.keepAliveInterval) clearInterval(this.keepAliveInterval)
            }
        }, keepAlivePeriodMs)
    }

    dispose() {
        if (this.keepAliveInterval) clearInterval(this.keepAliveInterval)
        // TODO: at this point we could close the session
    }
}

export class InfoProvider implements Disposable {
    private rpc?: Rpc;
    private api?: InfoviewApi;
    private serverNotifSubscriptions = new Map<string, [number, Disposable[]]>();
    private clientNotifSubscriptions = new Map<string, [number, Disposable[]]>();
    private disposables: Disposable[] = [];
    public isInitialized: boolean = false;
    private rpcSessions = new Map<string, RpcSessionAtPos>()

    dispose() {
        this.disposables.forEach(d => d.dispose());
        this.disposables = [];

        for (const [, [, subscriptions]] of this.serverNotifSubscriptions) {
            for (const h of subscriptions) {
                try {
                    h.dispose()
                } catch (e) {
                    wpl.log(`[InfoView] Could not dispose of server notification subscription: ${e}`);
                }
            }
        }
        this.serverNotifSubscriptions.clear();

        // dispose client notif subscriptions
        for (const [, [, subscriptions]] of this.clientNotifSubscriptions) {
            for (const h of subscriptions) {
                try {
                    h.dispose()
                } catch (e) {
                    wpl.log(`[InfoView] Could not dispose of client notification subscription: ${e}`);
                }
            }
        }
        this.clientNotifSubscriptions.clear();

        // dispose rpc sessions
        for (const [, sess] of this.rpcSessions) {
            try {
                sess.dispose()
            } catch (e) {
                wpl.log(`[InfoView] Could not dispose of RPC session: ${e}`);
            }
        }
        this.rpcSessions.clear();

        this.rpc = undefined;
        this.api = undefined;
    }

    /** Subscribe to emitters on client */
    private subscribeDidChangeNotification(client: LeanLspClient, method: string) {
        const h = client.didChange(params => {
            void this.api?.sentClientNotification?.(method, params);
        });
        return h;
    }

    private subscribeDidCloseNotification(client: LeanLspClient, method: string) {
        const h = client.didClose(params => {
            void this.api?.sentClientNotification?.(method, params)
        })
        return h
    }

    private subscribeDiagnosticsNotification(client: LeanLspClient, method: string) {
        const h = client.diagnostics(params => {
            void this.api?.gotServerNotification?.(method, params)
        })
        return h
    }

    private subscribeCustomNotification(client: LeanLspClient, method: string) {
        const h = client.customNotification(({ method: thisMethod, params }) => {
            if (thisMethod !== method) return
            void this.api?.gotServerNotification(method, params)
        })
        return h;
    }

    // Filters a list of hypotheses from an rpc response
    private filterHypotheses(hypotheses: any[]): any[] {
        switch (WaterproofConfigHelper.get(WaterproofSetting.VisibilityOfHypotheses)) {
            // Keep all hypotheses
            case "all":
                return hypotheses
            // Remove the hypotheses which type is simple 'text', in contrast to compound type which are arrays.
            case "limited":
                let filteredHyps = []
                for (let hyp of hypotheses) {
                    if ((hyp.type?.tag?.[1] !== undefined) && !('text' in hyp.type.tag[1])) {
                        filteredHyps.push(hyp)
                    }
                }
                return filteredHyps
            // Remove all hypotheses
            case "none":
                return []
        }
    }


    /** Api that is exposed to InfoView */
    private editorApi: EditorApi = {
        saveConfig: async (config: InfoviewConfig) => {
            try {
                const cfg = workspace.getConfiguration('lean4.infoview')
                // eslint-disable-next-line @typescript-eslint/no-explicit-any
                for (const [key, value] of Object.entries(config as Record<string, any>)) {
                    await cfg.update(key, value, ConfigurationTarget.Global)
                }
            } catch (e) {
                wpl.log(`[InfoProvider] saveConfig failed: ${e}`)
            }
        },

        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        sendClientRequest: async (_uri: string, method: string, params: any): Promise<any> => {
            const client = this.client.client
            if (client) {
                try {
                    const result = await this.client.client.sendRequest(method, params)

                    // Filter hypotheses in an rpc response depending on visibility setting
                    if (result !== null) {
                        switch (params.method) {
                            // Handling rpc requrest for all the goals
                            case "Lean.Widget.getInteractiveGoals":
                                for (let goal of result.goals) {
                                    goal.hyps = this.filterHypotheses(goal.hyps)
                                }
                                break;
                            // Handling rpc requrest for a specific goal
                            case "Lean.Widget.getInteractiveTermGoal":
                                result.hyps = this.filterHypotheses(result.hyps)
                        }
                    }

                    return result
                } catch (e) {
                    wpl.log(`[InfoProvider] Failed to send client request: ${e}`)
                }
            }
        },

        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        sendClientNotification: async (_uri: string, method: string, params: any): Promise<void> => {
            const client = this.client.client;
            if (client) {
                await this.client.client.sendNotification(method, params)
            }
        },

        subscribeServerNotifications: async (method: string) => {
            wpl.log(`[InfoProvider] subscribeServerNotifications ${method}`)

            const el = this.serverNotifSubscriptions.get(method)
            if (el) {
                const [count, subscriptions] = el
                this.serverNotifSubscriptions.set(method, [count + 1, subscriptions])
                return
            }

            if (method === 'textDocument/publishDiagnostics') {
                const subscriptions: Disposable[] = []
                subscriptions.push(this.subscribeDiagnosticsNotification(this.client, method))
                this.serverNotifSubscriptions.set(method, [1, subscriptions])
            } else if (method.startsWith('$')) {
                const subscriptions: Disposable[] = []
                subscriptions.push(this.subscribeCustomNotification(this.client, method))
                this.serverNotifSubscriptions.set(method, [1, subscriptions])
            } else {
                throw new Error(`subscription to ${method} server notifications not implemented`)
            }
        },
        unsubscribeServerNotifications: async (method: string) => {
            wpl.log(`[InfoProvider] unsubscribeServerNotifications, ${method}`)

            const el = this.serverNotifSubscriptions.get(method)
            if (!el) {
                console.warn(`[InfoProvider] unsubscribeServerNotifications: no subscription for ${method}`)
                return
            }

            const [count, subscriptions] = el
            if (count === 1) {
                for (const h of subscriptions) {
                    try {
                        h.dispose()
                    } catch (e) {
                        wpl.log(`[InfoView] Could not dispose of server notification subscription: ${e}`);
                    }
                }
                this.serverNotifSubscriptions.delete(method)
            } else {
                this.serverNotifSubscriptions.set(method, [count - 1, subscriptions])
            }
        },

        subscribeClientNotifications: async (method: string) => {
            wpl.log(`[InfoProvider] subscribeClientNotifications ${method}`)

            const el = this.clientNotifSubscriptions.get(method)
            if (el) {
                const [count, subscriptions] = el
                this.clientNotifSubscriptions.set(method, [count + 1, subscriptions])
                return
            }

            if (method === 'textDocument/didChange') {
                const subscriptions: Disposable[] = []
                subscriptions.push(this.subscribeDidChangeNotification(this.client, method))
                this.clientNotifSubscriptions.set(method, [1, subscriptions])
            } else if (method === 'textDocument/didClose') {
                const subscriptions: Disposable[] = []
                subscriptions.push(this.subscribeDidCloseNotification(this.client, method))
                this.clientNotifSubscriptions.set(method, [1, subscriptions])
            } else {
                throw new Error(`Subscription to '${method}' client notifications not implemented`)
            }
        },

        unsubscribeClientNotifications: async (method: string) => {
            wpl.log(`[InfoProvider] unsubscribeClientNotifications ${method}`)

            const el = this.clientNotifSubscriptions.get(method)
            if (!el) {
                return
            }

            const [count, subscriptions] = el
            if (count === 1) {
                for (const d of subscriptions) {
                    try {
                        d.dispose()
                    } catch (e) {
                        wpl.log(`[InfoView] Could not dispose of client notification subscription: ${e}`);
                    }
                }
                this.clientNotifSubscriptions.delete(method)
            } else {
                this.clientNotifSubscriptions.set(method, [count - 1, subscriptions])
            }
        },

        copyToClipboard: async text => {
            await env.clipboard.writeText(text)
        },

        insertText: async (_text, _kind, _tdpp) => {
            wpl.log(`[Infoprovider] Method "insertText" is not implemented`);
        },

        applyEdit: async (e: WorkspaceEdit) => {
            const document = this.client.activeDocument;
            if (!document || !this.client.webviewManager) {
                wpl.log(`[InfoProvider] Cannot apply edit: no active document or webviewManager`);
                return;
            }
            const uri = document.uri.toString();
            const changes = e.changes?.[uri];
            if (!changes || changes.length === 0) {
                wpl.log(`[InfoProvider] No changes for active document`);
                return;
            }
            for (const change of changes) {
                const start = document.offsetAt(
                    new Position(change.range.start.line, change.range.start.character)
                );
                const end = document.offsetAt(
                    new Position(change.range.end.line, change.range.end.character)
                );
                this.client.webviewManager.postMessage(uri, {
                    type: MessageType.replaceRange,
                    body: { start, end, text: change.newText }
                });
            }
        },

        showDocument: async _show => {
            // noop here
        },

        restartFile: async _uri => {
            wpl.log("[Infoprovider] This is not yet implemented")
        },

        createRpcSession: async uri => {
            wpl.log(`[Infoprovider] Creating rpc session for ${uri}`)
            const sessionId = await rpcConnect(this.client, uri)
            const session = new RpcSessionAtPos(this.client, sessionId, uri)
            this.rpcSessions.set(sessionId, session)
            return sessionId
        },

        closeRpcSession: async sessionId => {
            wpl.log(`[Infoprovider] Close rpc session: ${sessionId}`)
            const sess = this.rpcSessions.get(sessionId)
            if (sess) {
                sess.dispose()
                this.rpcSessions.delete(sessionId)
            }
        },
    }

    constructor(private client: LeanLspClient, panel: GoalsPanel) {
        const rpc = new Rpc(m => panel.postMessage(m));
        rpc.register(this.editorApi);
        this.rpc = rpc;
        this.api = rpc.getApi();

        const sub = panel.on(WebviewEvents.message, (msg) => {
            if (msg.type !== MessageType.infoviewRpc) return;
            this.rpc?.messageReceived(msg.body);
        });

        this.disposables.push(sub);

        client.clientStopped((reason) => {
            void this.onClientStopped(reason)
        });
    }

    /**
     * Initiallizes InfoView through sending server restarted message
     * @param loc location at current document
     * @returns
     */
    public async initInfoview(loc: Location) {
        const api = this.api;
        if (!api) {
            return;
        }
        await api.initialize(loc);

        if (this.client.client.initializeResult) {
            this.resetServerState();
            await this.sendPosition(loc);
        }
        this.isInitialized = true;
    }

    /**
     * Helper to (re-)initialize InfoView
     */
    public async resetServerState(): Promise<void> {
        if (this.client.client.initializeResult) {
            await this.api?.serverStopped(undefined);
            await this.api?.serverRestarted(this.client.client.initializeResult);
        }
    }

    /**
     * Sends the location in current document to InfoView through `InfoviewApi`
     * @param loc Location in the document
     */
    public async sendPosition(loc: Location) {
        await this.api?.changedCursorLocation(loc)
    }

    private async onClientStopped(reason: ServerStoppedReason){
        await this.api?.serverStopped(reason);
    }

}
