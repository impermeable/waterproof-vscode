import { DocChange, WrappingDocChange } from "@impermeable/waterproof-editor";
import { Tree } from "./Tree";
/**
 * The type returned by the functions converting steps to Document Changes of the
 * underlying vscode model of the document
 */
export type ParsedStep = {
    /** The document change that will be forwarded to vscode */
    result: DocChange | WrappingDocChange;
    /** The new tree that represents the updated mapping */
    newTree: Tree
}

/**
 * In prosemirror, every step is a replace step. This enum is used to classify 
 * the steps into the given 'pure' operations
 */
export enum OperationType {
    insert = "insert",
    delete = "delete",
    replace = "replace"
};