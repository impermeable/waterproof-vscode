import { DocChange, WrappingDocChange } from "waterproof-editor/api";
import { Message, MessageType } from "../../shared";


/**
	 * If the file starts with a coqblock or ends with a coqblock this function adds a newline to the start for
	 * insertion purposes
	 * @param content the content of the file
	 */
export function checkPrePost(content: string): { resultingDocument: string, documentChange: WrappingDocChange | DocChange | undefined} {
    let result = content
    const edit1: DocChange = {startInFile: 0, endInFile: 0,finalText: ''};
    const edit2: DocChange = {startInFile: content.length, endInFile: content.length, finalText: ''};
    if (content.startsWith("```coq\n")) {
        result = '\n' + result;
        edit1.finalText = '\n';
    }
    if (content.endsWith("\n```")) {
        result = result + '\n';
        edit2.finalText = '\n';
    }
    const final: WrappingDocChange = { firstEdit: edit1, secondEdit: edit2};
    if (edit1.finalText == '\n' || edit2.finalText == '\n') return { resultingDocument: result, documentChange: final };
    return { resultingDocument: result, documentChange: undefined };
}

// TODO: Temporary fix for the bug that "<z" turns into an html tag.
export function fixLessThanBug(content: string, post: (m : Message) => void): string {
    const regexp = /<(?!input-area|hint|br|hr)([\w\d]+)/g;
    const matches = content.matchAll(regexp);
    let newContent = content;
    for (const match of matches) {
        if (match.index === undefined) continue;
        newContent = newContent.substring(0, match.index + 1) + " " + newContent.substring(match.index + 1);

        const edit: DocChange = { startInFile: match.index+1, endInFile: match.index+1, finalText: " "};
        post({type: MessageType.docChange, body: edit});
    }
    return newContent;
}