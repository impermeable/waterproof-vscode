import { EditorView } from "@codemirror/view";
import themeJSON from "./editorTheme.json";

/**
 * Inspired by:
 * https://github.com/codemirror/theme-one-dark/blob/main/src/one-dark.ts
 * 
 * Used for theming the markdown editors, differs from the one in color-scheme.ts.
 */
export const editorTheme = EditorView.theme(themeJSON, {dark: true});