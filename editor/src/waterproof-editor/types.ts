import { Step } from "prosemirror-transform";
import { DocChange, WrappingDocChange } from "../../../shared";
import { Block } from "./document";
import { StringCell } from "../mapping/mvFile/types";

export type Positioned<A> = {
    obj: A;
    pos: number | undefined;
};

export type WaterproofDocument = Block[];

export type WaterproofCallbacks = {
    executeCommand: (command: string, time: number) => void,
    editorReady: () => void,
    documentChange: (change: DocChange | WrappingDocChange) => void,
    applyStepError: (errorMessage: string) => void,
    cursorChange: (cursorPosition: number) => void
    lineNumbers: (linenumbers: Array<number>, version: number) => void,
}

export abstract class WaterproofMapping {
    abstract getMapping: () => Map<number, StringCell>;
    abstract get version(): number;
    abstract findPosition: (index: number) => number;
    abstract findInvPosition: (index: number) => number;
    abstract update: (step: Step) => DocChange | WrappingDocChange;
}

export type WaterproofEditorConfig = {
    api: WaterproofCallbacks,
    documentConstructor: (document: string) => WaterproofDocument,
    mapping: new (inputString: string, versionNum: number) => WaterproofMapping
}