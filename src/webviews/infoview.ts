import {
    EditorApi,
    InfoviewApi,
    // InfoviewConfig,
    // LeanFileProgressParams,
    // RpcConnected,
    // RpcConnectParams,
    // RpcErrorCode,
    // RpcKeepAliveParams,
    // ServerStoppedReason,
    // TextInsertKind,
} from '@leanprover/infoview-api'
import { CoqWebview, WebviewState } from './coqWebview';
import { Rpc } from '../helpers/rpc';
import { ExtensionContext } from 'vscode';

export class LeanInfoviewWebview extends CoqWebview {
    // private rpc: Rpc;
    // private api: InfoviewApi;
    constructor(context: ExtensionContext) {
        super(context.extensionUri, "infoview", false);
    }
    
    //TODO: handle messages
    


}