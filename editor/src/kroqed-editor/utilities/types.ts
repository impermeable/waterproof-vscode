import { DocChange, WrappingDocChange } from "../../../../shared";


export type Positioned<A> = {
    obj: A;
    pos: number | undefined;
};

export type WaterproofEditorConfig = {
    api: {
        executeCommand: (command: string, time: number) => void,
        editorReady: () => void,
        documentChange: (change: DocChange | WrappingDocChange) => void,
        applyStepError: (errorMessage: string) => void,
        cursorChange: (cursorPosition: number) => void
        lineNumbers: (linenumbers: Array<number>, version: number) => void,
    }
}