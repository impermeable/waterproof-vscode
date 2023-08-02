import { WorkspaceEdit, workspace } from "vscode";

type EditOperation = (e: WorkspaceEdit) => void;

/**
 * A utility class that allows you to make workspace edits, which are asynchronously applied in the
 * original order.
 */
export class SequentialEditor {

    private inProgress = false;
    private readonly queue: EditOperation[] = [];
    private finishListener?: () => void;

    /**
     * Whether the queue contains pending operations or there is an ongoing workspace edit.
     */
    get isInProgress() {
        return this.inProgress;
    }

    /**
     * Applies the next (i.e., first) operation in the `queue` if it is not empty. Otherwise signals
     * that the sequence of edits is finished.
     */
    private applyNext() {
        if (this.queue.length) {
            this.apply(this.queue.shift()!);
        } else {
            this.finishListener?.();
            this.inProgress = false;
        }
    }

    /**
     * Applies `op` to the workspace, and then (recursively) applies the remaining operations in the
     * queue.
     */
    private apply(op: EditOperation) {
        const edit = new WorkspaceEdit();
        op(edit);
        workspace.applyEdit(edit).then(() => {
            this.applyNext();
        });
    }

    /**
     * Enqueues the specified operation to the edit queue. It is guaranteed that operations are
     * applied in the same order that they were enqueued.
     */
    edit(op: EditOperation) {
        if (this.inProgress) {
            this.queue.push(op);
        } else {
            this.inProgress = true;
            this.apply(op);
        }
    }

    /**
     * Registers a handler that is called whenever all enqueued operations have been applied.
     */
    onFinish(listener: () => void) {
        this.finishListener = listener;
    }

}
