import { Uri, env, window } from "vscode";

export namespace WaterproofErrors {
    export function showError(message: string) {
        window.showErrorMessage(message, REPORT_ISSUE).then(reportIssueHandler);
    }
}

const reportIssueHandler = (value: typeof REPORT_ISSUE | undefined) => {
    if (value === REPORT_ISSUE) {
        env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-vscode/issues"));
    }
} 

const REPORT_ISSUE = "Report Issue";