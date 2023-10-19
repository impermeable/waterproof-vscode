import { Uri, env } from "vscode";

export const reportIssueHandler = (value: typeof REPORT_ISSUE | undefined) => {
    env.openExternal(Uri.parse("https://github.com/impermeable/waterproof-vscode/issues"));
} 

export const REPORT_ISSUE = "Report Issue";