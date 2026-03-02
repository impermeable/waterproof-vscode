import { defaultToMarkdown } from "@impermeable/waterproof-editor";

/**
 * Translates the Markdown from the Waterproof Lean verso genre into markdown compatible syntax.
 * @param input A string of Markdown in the Waterproof Lean verso genre.
 * @returns A string of valid Markdown with inline math replaced.
 */
export function versoMarkdownToMarkdown(input: string): string {
    return defaultToMarkdown(input.replaceAll(/\$`([\s\S]*?)`/g, "$$$1$$"));
}