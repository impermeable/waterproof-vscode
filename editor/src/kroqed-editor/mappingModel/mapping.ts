import { Step } from "prosemirror-transform";
import { DocChange, FileFormat, WrappingDocChange } from "../../../../shared";
import { TextDocMappingMV } from "./mvFile";
import { TextDocMappingV } from "./vFile";

export class TextDocMapping {
    private _theMapping: TextDocMappingMV | TextDocMappingV;
    
    constructor (fileFormat: FileFormat, inputString: string, version: number) {
        if (fileFormat === FileFormat.RegularV) {
            this._theMapping = new TextDocMappingV(inputString, version);
        } else if (fileFormat === FileFormat.MarkdownV) {
            this._theMapping = new TextDocMappingMV(inputString, version);
        } else {
            throw new Error("Unsupported file format passed to TextDocMapping.");
        }
    }

    public getMapping() {
        return this._theMapping.getMapping();
    }

    public get version() {
        return this._theMapping.version;
    }

    public findPosition(index: number) { 
        return this._theMapping.findPosition(index) 
    }

    public findInvPosition(index: number) {
        return this._theMapping.findInvPosition(index);
    }

    public stepUpdate(step: Step): DocChange | WrappingDocChange {
        return this._theMapping.stepUpdate(step);
    }
}