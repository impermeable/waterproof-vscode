import {
    EditorApi,
    InfoviewApi,
    InfoviewConfig,
    LeanFileProgressParams,
    RpcConnected,
    RpcConnectParams,
    RpcErrorCode,
    RpcKeepAliveParams,
    ServerStoppedReason,
    TextInsertKind,
} from '@leanprover/infoview-api'
import { Rpc } from './helpers/rpc';
import { Message, MessageType } from '../shared';
import {
    commands,
    ConfigurationTarget,
    Diagnostic,
    Disposable,
    env,
    ExtensionContext,
    Position,
    Range,
    Selection,
    TextDocument,
    TextEditor,
    TextEditorRevealType,
    Uri,
    WebviewPanel,
    window,
    workspace,
} from 'vscode'
import { LeanLspClient } from './lsp-client/leanlspclient';
import { DocumentUri, WorkspaceEdit, Location } from 'vscode-languageserver-protocol';
import { GoalsPanel } from './webviews/goalviews/goalsPanel';

const keepAlivePeriodMs = 10000

// Connects client to server and returns result
async function rpcConnect(client: LeanLspClient, uri: DocumentUri): Promise<string> {
    const connParams: RpcConnectParams = { uri }
    const result: RpcConnected = await client.sendRequest('$/lean/rpc/connect', connParams)
    return result.sessionId
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
        this.client = client
        this.keepAliveInterval = setInterval(async () => {
            const params: RpcKeepAliveParams = { uri, sessionId }
            try {
                await client.sendNotification('$/lean/rpc/keepAlive', params)
            } catch (e) {
                console.log(`[InfoProvider] failed to send keepalive for ${uri}: ${e}`)
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
    private client!: LeanLspClient;
    private rpc?: Rpc;
    private api?: InfoviewApi;
    private serverNotifSubscriptions = new Map<string, [number, Disposable[]]>();
    private disposables: Disposable[] = [];
    public isInitialized: boolean = false;
    private rpcSessions = new Map<string, RpcSessionAtPos>()

    constructor(
        private cl: LeanLspClient
    ) {
        this.client = cl;
    }

    attachHost(panel: GoalsPanel | undefined) {
        if (!panel) {
            return;
        }
        const rpc = new Rpc(m => panel.postMessage(m));
        rpc.register(this.editorApi);
        this.rpc = rpc;
        this.api = rpc.getApi();

        const disp = panel.onInfoviewMes(m => {
            try {
                this.rpc?.messageReceived(m.body);
            } catch (e) {
                console.error("infoview rpc.messageReceived failed", e);
            }
        });

        this.disposables.push(disp);
    }

    dispose() {
        this.disposables.forEach(d => d.dispose());
        this.disposables = [];
        this.rpc = undefined;
        this.api = undefined;
    }
    // private subscribeDidChangeNotification(client: LeanLspClient, method: string) {
    //     const h = client.didChange(params => {
    //         void this.api.sentClientNotification(method, params)
    //     })
    //     return h
    // }

    // private subscribeDidCloseNotification(client: LeanLspClient, method: string) {
    //     const h = client.didClose(params => {
    //         void this.api.sentClientNotification(method, params)
    //     })
    //     return h
    // }

    // private subscribeDiagnosticsNotification(client: LeanLspClient, method: string) {
    //     const h = client.diagnostics(params => {
    //         void this.api.gotServerNotification(method, params)
    //     })
    //     return h
    // }

    // private subscribeCustomNotification(client: LeanLspClient, method: string) {
    //     const h = client.customNotification(({ method: thisMethod, params }) => {
    //         if (thisMethod !== method) return
    //         void this.api.gotServerNotification(method, params)
    //     })
    //     return h
    // }

    private editorApi: EditorApi = {
        saveConfig: async (config: InfoviewConfig) => {
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('allErrorsOnLine', config.allErrorsOnLine, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('autoOpenShowsGoal', config.autoOpenShowsGoal, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('debounceTime', config.debounceTime, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('expectedTypeVisibility', config.expectedTypeVisibility, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('showGoalNames', config.showGoalNames, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('emphasizeFirstGoal', config.emphasizeFirstGoal, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('reverseTacticState', config.reverseTacticState, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('hideTypeAssumptions', config.hideTypeAssumptions, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('hideInstanceAssumptions', config.hideInstanceAssumptions, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('hideInaccessibleAssumptions', config.hideInaccessibleAssumptions, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('hideLetValues', config.hideLetValues, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('showTooltipOnHover', config.showTooltipOnHover, ConfigurationTarget.Global)
            // await workspace
            //     .getConfiguration('lean4.infoview')
            //     .update('messageOrder', config.messageOrder, ConfigurationTarget.Global)
        },
        sendClientRequest: async (uri: string, method: string, params: any): Promise<any> => {
            const client = this.client
            if (client) {
                try {
                    const result = await client.sendRequest(method, params)
                    return result
                } catch (ex: any) {
                    if (ex.code === RpcErrorCode.WorkerCrashed) {
                        // ex codes related with worker exited or crashed
                        console.log(`[InfoProvider]The Lean Server has stopped processing this file: ${ex.message}`)
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
            const client = this.client;
            if (client) {
                await client.sendNotification(method, params)
            }
        },
        subscribeServerNotifications: async method => {
            const el = this.serverNotifSubscriptions.get(method);
            // Bookkeeping
            if (el) {
                const [count, h] = el
                this.serverNotifSubscriptions.set(method, [count + 1, h])
            }
            console.log('[InfoviewHost] subscribeServerNotifications', method);

            // if (method === 'textDocument/publishDiagnostics') {
            //     const subscriptions: Disposable[] = []
            //     for (const client of this.clientProvider.getClients()) {
            //         subscriptions.push(this.subscribeDiagnosticsNotification(client, method))
            //     }
            //     this.serverNotifSubscriptions.set(method, [1, subscriptions])
            // } else if (method.startsWith('$')) {
            //     const subscriptions: Disposable[] = []
            //     for (const client of this.clientProvider.getClients()) {
            //         subscriptions.push(this.subscribeCustomNotification(client, method))
            //     }
            //     this.serverNotifSubscriptions.set(method, [1, subscriptions])
            // } else {
            //     throw new Error(`subscription to ${method} server notifications not implemented`)
            // }



            // one subscription to the lean client
            // const disposable = this.subscribeServer(method, params => {
            //     // forward to the webview
            //     void this.api.gotServerNotification(method, params);
            // });

            // this.serverNotifSubscriptions.set(method, { refCount: 1, disposable });

        },
        unsubscribeServerNotifications: async method => {
            // const el = this.serverNotifSubscriptions.get(method)
            // if (!el) throw new Error(`trying to unsubscribe from '${method}' with no active subscriptions`)
            // const [count, subscriptions] = el
            // if (count === 1) {
            //     for (const h of subscriptions) {
            //         h.dispose()
            //     }
            //     this.serverNotifSubscriptions.delete(method)
            // } else {
            //     this.serverNotifSubscriptions.set(method, [count - 1, subscriptions])
            // }
            console.log('[InfoviewHost] unsubscribeServerNotifications', method);
        },

        subscribeClientNotifications: async method => {
            console.log('[InfoviewHost] subscribeClientNotifications', method);
            // const el = this.clientNotifSubscriptions.get(method)
            // if (el) {
            //     const [count, d] = el
            //     this.clientNotifSubscriptions.set(method, [count + 1, d])
            //     return
            // }

            // if (method === 'textDocument/didChange') {
            //     const subscriptions: Disposable[] = []
            //     for (const client of this.clientProvider.getClients()) {
            //         subscriptions.push(this.subscribeDidChangeNotification(client, method))
            //     }
            //     this.clientNotifSubscriptions.set(method, [1, subscriptions])
            // } else if (method === 'textDocument/didClose') {
            //     const subscriptions: Disposable[] = []
            //     for (const client of this.clientProvider.getClients()) {
            //         subscriptions.push(this.subscribeDidCloseNotification(client, method))
            //     }
            //     this.clientNotifSubscriptions.set(method, [1, subscriptions])
            // } else {
            //     throw new Error(`Subscription to '${method}' client notifications not implemented`)
            // }
        },

        unsubscribeClientNotifications: async method => {
            console.log('[InfoviewHost] unsubscribeClientNotifications', method);
            // const el = this.clientNotifSubscriptions.get(method)
            // if (!el) throw new Error(`trying to unsubscribe from '${method}' with no active subscriptions`)
            // const [count, subscriptions] = el
            // if (count === 1) {
            //     for (const d of subscriptions) {
            //         d.dispose()
            //     }
            //     this.clientNotifSubscriptions.delete(method)
            // } else {
            //     this.clientNotifSubscriptions.set(method, [count - 1, subscriptions])
            // }
        },
        copyToClipboard: async text => {
            await env.clipboard.writeText(text)
            // displayNotification('Information', `Copied to clipboard: ${text}`)
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
            // const uri = parseExtUri(show.uri)
            // if (uri === undefined) {
            //     return
            // }
            // void this.revealEditorSelection(uri, p2cConverter.asRange(show.selection))
        },
        restartFile: async uri => {
            // TODO: restart the file, first needs to be implemented on the client side
            console.log("This is not yet implemented")
            // const extUri = parseExtUri(uri)
            // if (extUri === undefined) {
            //     return
            // }
            // this.clientProvider.restartFile(extUri)
        },

        createRpcSession: async uri => {
            const client = this.client
            if (!client) {
                throw new Error('No active Lean client')
            }
            const connParams = { uri }
            const result = await client.sendRequest('$/lean/rpc/connect', connParams)
            const sessionId = result.sessionId
            const session = new RpcSessionAtPos(client, sessionId, uri)
            this.rpcSessions.set(sessionId, session)
            return sessionId
        },
        closeRpcSession: async sessionId => {
            console.log(`Close infoview session: ${sessionId}`)
            const sess = this.rpcSessions.get(sessionId)
            if (sess) {
                sess.dispose()
                this.rpcSessions.delete(sessionId)
            }
        },
    }

    public async initInfoview(loc: Location) {
        const api = this.api;
        if (!api) {
            return;
        }
        await api.initialize(loc);

        if (this.client.initializeResult) {
            // await this.sendConfig();
            await api.serverStopped(undefined);
            await api.serverRestarted(this.client.initializeResult);
            // await this.sendDiagnostics();
            // await this.sendProgress();
            await this.sendPosition(loc);
        }
        this.isInitialized = true;
    }

    public async sendPosition(loc: Location) {
        await this.api?.changedCursorLocation(loc)
    }



}