import { ReplaceAroundStep, ReplaceStep } from "@impermeable/waterproof-editor";
import { OperationType } from "./types";


export function typeFromStep(step: ReplaceStep | ReplaceAroundStep): OperationType {
    if (step.from == step.to) return OperationType.insert;
    if (step.slice.content.firstChild == null) {
        return OperationType.delete;
    } else {
        return OperationType.replace;
    }
}