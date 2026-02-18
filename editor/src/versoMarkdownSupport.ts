import { defaultToMarkdown } from "@impermeable/waterproof-editor";


export function versoMarkdownToMarkdown(input: string): string {
    console.log("WWOOOOOOO");
    return defaultToMarkdown(input.replaceAll(/\$`([\s\S]*?)`/g, "$$$1$$"));
}