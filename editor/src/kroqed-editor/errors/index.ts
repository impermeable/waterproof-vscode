import { DiagnosticMessage } from "../../../../shared/Messages";
import { EditorView } from "prosemirror-view";
import { EditorView as CM_EditorView } from "@codemirror/view";
import { TextDocMapping } from "../mappingModel";
import { COQ_CODE_PLUGIN_KEY } from "../codeview/coqcodeplugin";
import { CodeBlockView } from "../codeview/nodeview";
import { Diagnostic } from "@codemirror/lint";




// Convert error ranges.
// Find out what view they belong to?
//

const SEVERITY_STRINGS = ["error", "warning", "info", "hint"];

type Severity = "error" | "warning" | "info" | "hint";
const severityToString = (severity: number): Severity => {
    if (severity > 3) return SEVERITY_STRINGS[0] as Severity;
    return SEVERITY_STRINGS[severity] as Severity;
} 

export class ErrorManager {
    private currentDiagnostics: Array<Diagnostic>;

    constructor() {
        this.currentDiagnostics = Array<Diagnostic>();
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

        // Create a view with pos array
        const viewsWithPos: Array<{pos: number | undefined, view: CodeBlockView}> = Array.from(views).map((value) => { 
            return {pos: value._getPos(), view: value}; 
        });

        // Convert to inverse mapped positions.
        const doc = view.state.doc;
        this.currentDiagnostics = new Array<Diagnostic>();
        for (let diag of diagnostics) {
            
            // Compute start and end positions.
            const start = map.findInvPosition(diag.startOffset);
            const end = map.findInvPosition(diag.endOffset);
            
            // Skip diagnostic if the start position is greater than or equal to the end.
            if (start >= end) {
                console.error("Start is greater than end");
                continue;
            }

            const $start = doc.resolve(start);
            const $end = doc.resolve(end);

            if (!$start.sameParent($end)) {
                console.error("We do not support multi line errors");
                continue;
            }
            
            // Create a new diagnostic object.
            const newDiagnostic: Diagnostic = {
                // TODO: Look into the renderMessage function.
                from: $start.parentOffset,
                to: $end.parentOffset,
                message: diag.message,
                severity: severityToString(diag.severity),
                actions: [{
                    name: "Copy 📋", 
                    apply(view: CM_EditorView, from: number, to: number) {
                        navigator.clipboard.writeText(diag.message);
                    }
                }]
            }

            let theView: CodeBlockView | undefined = undefined;
            let pos = view.state.doc.content.size;
            for(const obj of viewsWithPos) {
                if (obj.pos === undefined) continue;
                if(start - obj.pos < pos && obj.pos < start) {
                    pos = start - obj.pos;
                    theView = obj.view;
                }
            }

            if (theView === undefined) throw new Error("Diagnostic message does not match any coqblock");
            theView.addCoqError(newDiagnostic);
        } 
        for (const view of views) view.forceUpdateLinting();
    }

    public getDiagnosticsInRange(low: number, high: number): Array<Diagnostic> {
        return this.currentDiagnostics.filter((value) => {
            return ((low <= value.from) && (value.to <= high));
        });
    }

    public rangeContainsError(low: number, high: number): boolean {
        return false;
    }
}
