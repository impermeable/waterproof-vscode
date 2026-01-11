import {
    EditorApi,
    InfoviewApi,
    InfoviewConfig,
    RpcConnected,
    RpcConnectParams,
    RpcErrorCode,
    RpcKeepAliveParams,
    ServerStoppedReason,
} from '@leanprover/infoview-api'
import { Rpc } from './helpers/rpc';
import { MessageType } from '../shared';
import {
    ConfigurationTarget,
    Disposable,
    env,
    workspace,
} from 'vscode'
import { LeanLspClient } from './lsp-client/lean';
import { DocumentUri, WorkspaceEdit, Location } from 'vscode-languageserver-protocol';
import { GoalsPanel } from './webviews/goalviews/goalsPanel';
import { WaterproofLogger as wpl } from './helpers';
import { WebviewEvents } from './webviews/coqWebview';

const keepAlivePeriodMs = 10000

// Connects client to server and returns result
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

// The class for rpc session for some position at the document
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
                try { h.dispose() } catch {}
            }
        }
        this.serverNotifSubscriptions.clear();

        // dispose client notif subscriptions
        for (const [, [, subscriptions]] of this.clientNotifSubscriptions) {
            for (const h of subscriptions) {
                try { h.dispose() } catch {}
            }
        }
        this.clientNotifSubscriptions.clear();

        // dispose rpc sessions
        for (const [, sess] of this.rpcSessions) {
            try { sess.dispose() } catch {}
        }
        this.rpcSessions.clear();

        this.rpc = undefined;
        this.api = undefined;
    }

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

    // private handleClientNotification(client: LeanLspClient, method: string, params: any) {
    //     this.rpc?.notify?.('clientNotification', { method, params })
    // }

    private editorApi: EditorApi = {
        saveConfig: async (config: InfoviewConfig) => {
            try {
                const cfg = workspace.getConfiguration('lean4.infoview')
                for (const [key, value] of Object.entries(config as Record<string, any>)) {
                    await cfg.update(key, value, ConfigurationTarget.Global)
                }
            } catch (e) {
                console.error('[InfoProvider] saveConfig failed', e)
            }
        },

        sendClientRequest: async (uri: string, method: string, params: any): Promise<any> => {
            const client = this.client.client
            if (client) {
                try {
                    const result = await this.client.client.sendRequest(method, params)
                    return result
                } catch (ex: any) {
                    if (ex.code === RpcErrorCode.WorkerCrashed) {
                        // ex codes related with worker exited or crashed
                        wpl.log(`[InfoProvider]The Lean Server has stopped processing this file: ${ex.message}`)
                        // await this.onWorkerStopped(uri, client, {
                        //     message: 'The Lean Server has stopped processing this file: ',
                        //     reason: ex.message as string,
                        // })
                    }
                    throw ex
                }
            }
            throw Error('No active Lean client.')
        },

        sendClientNotification: async (uri: string, method: string, params: any): Promise<void> => {
            const client = this.client.client;
            if (client) {
                await this.client.client.sendNotification(method, params)
            }
        },

        subscribeServerNotifications: async (method: string) => {
            wpl.log(`[InfoviewHost] subscribeServerNotifications ${method}`)

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
            wpl.log(`[InfoviewHost] unsubscribeServerNotifications, ${method}`)

            const el = this.serverNotifSubscriptions.get(method)
            if (!el) {
                console.warn(`[InfoviewHost] unsubscribeServerNotifications: no subscription for ${method}`)
                return
            }

            const [count, subscriptions] = el
            if (count === 1) {
                for (const h of subscriptions) {
                    try { h.dispose() } catch {}
                }
                this.serverNotifSubscriptions.delete(method)
            } else {
                this.serverNotifSubscriptions.set(method, [count - 1, subscriptions])
            }
        },

        subscribeClientNotifications: async (method: string) => {
            wpl.log(`[InfoviewHost] subscribeClientNotifications ${method}`)

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
            wpl.log(`[InfoviewHost] unsubscribeClientNotifications ${method}`)

            const el = this.clientNotifSubscriptions.get(method)
            if (!el) {
                console.warn(`[InfoviewHost] unsubscribeClientNotifications: no subscription for ${method}`)
                return
            }

            const [count, subscriptions] = el
            if (count === 1) {
                for (const d of subscriptions) {
                    try { d.dispose() } catch {}
                }
                this.clientNotifSubscriptions.delete(method)
            } else {
                this.clientNotifSubscriptions.set(method, [count - 1, subscriptions])
            }
        },


        copyToClipboard: async text => {
            await env.clipboard.writeText(text)
        },
        insertText: async (text, kind, tdpp) => {
            // let uri: ExtUri | undefined
            // let pos: Position | undefined
            // if (tdpp) {
            //     uri = toExtUri(p2cConverter.asUri(tdpp.textDocument.uri))
            //     if (uri === undefined) {
            //         return
            //     }
            //     pos = p2cConverter.asPosition(tdpp.position)
            // }
            // await this.handleInsertText(text, kind, uri, pos)
        },
        applyEdit: async (e: WorkspaceEdit) => {
            // const we = await p2cConverter.asWorkspaceEdit(e)
            // await workspace.applyEdit(we)
        },
        showDocument: async show => {
            // noop here
        },
        restartFile: async uri => {
            wpl.log("This is not yet implemented")
        },

        createRpcSession: async uri => {
            wpl.log(`[Infoprovider] Creating rpc session for ${uri}`)
            const sessionId = await rpcConnect(this.client, uri)
            const session = new RpcSessionAtPos(this.client, sessionId, uri)
            this.rpcSessions.set(sessionId, session)
            return sessionId
        },
        closeRpcSession: async sessionId => {
            wpl.log(`Close rpc session: ${sessionId}`)
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

    public async initInfoview(loc: Location) {
        const api = this.api;
        if (!api) {
            return;
        }
        await api.initialize(loc);

        if (this.client.client.initializeResult) {
            await api.serverStopped(undefined);
            await api.serverRestarted(this.client.client.initializeResult);
            await this.sendPosition(loc);
        }
        this.isInitialized = true;
    }

    public async sendPosition(loc: Location) {
        await this.api?.changedCursorLocation(loc)
    }

    private async onClientStopped(reason: ServerStoppedReason){
        await this.api?.serverStopped(reason);
    }

}
