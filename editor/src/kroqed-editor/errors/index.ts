import { ResolvedPos } from "prosemirror-model";
import { DiagnosticMessage } from "../../../../shared/Messages";
import { DiagnosticSeverity } from "vscode";
import { EditorView } from "prosemirror-view";
import { TextDocMapping } from "../mappingModel";
import { COQ_CODE_PLUGIN_KEY } from "../codeview/coqcodeplugin";
import { CodeBlockView } from "../codeview/nodeview";




// Convert error ranges.
// Find out what view they belong to?
//

/** Type that contains a coq diagnostics object fit for use in the ProseMirror editor context. */
type ProseDiagnostics = {message: string, start: number, end: number, $start: ResolvedPos, $end: ResolvedPos, severity: DiagnosticSeverity};

export class ErrorManager {
    private currentDiagnostics: Array<ProseDiagnostics>;

    constructor() {
        this.currentDiagnostics = Array<ProseDiagnostics>();
    }

    
    /**
     * Function that parses coq errors for use with Prose-/CodeMirror.
     * @param msg The DiagnosticMessage object
     */
    async parseCoqDiagnostics(msg: DiagnosticMessage, view: EditorView | undefined, mapping: TextDocMapping | undefined) {
        // Early return if there are mapping issues
        if (mapping === undefined || msg.version < mapping.version) return;

        let diagnostics = msg.positionedDiagnostics;
        const map = mapping;
        if (view === undefined || map === undefined) return;

        // Get the available coq views
        const views = COQ_CODE_PLUGIN_KEY.getState(view.state)?.activeNodeViews;
        if (views === undefined) return;
        // Clear the errors
        for (let view of views) view.clearCoqErrors();

        // Convert to inverse mapped positions.
        const doc = view.state.doc;
        this.currentDiagnostics = new Array<ProseDiagnostics>();
        for (let diag of diagnostics) {
            const start = map.findInvPosition(diag.startOffset);
            const end = map.findInvPosition(diag.endOffset);
            if (start >= end) continue;
            this.currentDiagnostics.push({
                message: diag.message,
                start,
                $start: doc.resolve(start),
                end,
                $end: doc.resolve(end),
                severity: diag.severity
            });
        }

        // Create a view with pos array
        const viewsWithPos = new Array<{pos: number | undefined, view: CodeBlockView}>();
        for (let view of views) viewsWithPos.push({pos: view._getPos(), view});


        for (const diag of this.currentDiagnostics) {
            if (!diag.$start.sameParent(diag.$end)) {
                console.error("We do not support multi line errors");
                continue;
            }
            if (diag.start > diag.end) {
                console.error("We do not support errors for which the start position is greater than the end postion.");
                continue;
            }
            let theView: CodeBlockView | undefined = undefined;
            let pos = view.state.doc.content.size;
            for(const obj of viewsWithPos) {
                if (obj.pos === undefined) continue;
                if(diag.start - obj.pos < pos && obj.pos < diag.start) {
                    pos = diag.start - obj.pos;
                    theView = obj.view;
                }
            }

            if (theView === undefined) throw new Error("Diagnostic message does not match any coqblock");
            theView.addCoqError(diag.$start.parentOffset, diag.$end.parentOffset, diag.message, diag.severity);
        }
    }

    public getDiagnosticsInRange(low: number, high: number): Array<ProseDiagnostics> {
        return this.currentDiagnostics.filter((value) => {
            return ((low <= value.start) && (value.end <= high));
        });
    }

    public rangeContainsError(low: number, high: number): boolean {
        return false;
    }
}
