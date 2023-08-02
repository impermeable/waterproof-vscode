import { EditorView, Decoration, DecorationSet } from "@codemirror/view"
import { StateField, StateEffect } from "@codemirror/state"

// Simple coq error mark. Styled in `color-scheme.ts`
const coqErrorMarkWithOptions = (message: string, severity: number) => {
    let cssClass = "cm-coq-";
    switch (severity) {
        case 0:
            cssClass += "error";
            break;
        case 1: 
            cssClass += "warning";
            break;
        case 2:
            cssClass += "info";
            break;
        case 3:
            cssClass += "hint";
            break;
    }
    return Decoration.mark({ class: cssClass, attributes: {title: message} });
}

/////// Transaction effects ///////

/** Transaction effect for adding a coq error.*/
const addCoqErrorTransactionEffect = StateEffect.define<CoqErrorRangeWithOptions>({
    map(value: CoqErrorRangeWithOptions, mapping) {
        return { 
            from: mapping.mapPos(value.from), 
            to: mapping.mapPos(value.to),
            message: value.message,
            severity: value.severity
        }
    }
});

/** Transaction effect for removing a coq error. */
const removeCoqErrorTransactionEffect = StateEffect.define<CoqErrorRange>({});

/** Transaction effect for clearing all coq errors. */
const clearCoqErrorsTransactionEffect = StateEffect.define({});

/**
 * The state field storing the coq error decorations.
 */
const coqErrorStateField = StateField.define<DecorationSet>({
    create() {
        // When creating the state field, set decorations to empty.
        return Decoration.none
    },
    update(underlines, tr) {
        // Update the set of decorations, 
        // by firstly mapping the changes over the existing set. 
        underlines = underlines.map(tr.changes);
        for (const effect of tr.effects) {
            if (effect.is(addCoqErrorTransactionEffect)) {
                underlines = underlines.update({
                    add: [coqErrorMarkWithOptions(effect.value.message, 
                        effect.value.severity).range(effect.value.from, effect.value.to)]
                });
            } else if (effect.is(removeCoqErrorTransactionEffect)) {
                underlines = underlines.update({
                    filter(from, to, value) {
                        return !(effect.value.from === from && effect.value.to === to);
                    },
                })
            } else if (effect.is(clearCoqErrorsTransactionEffect)) {
                underlines = Decoration.none;
            }
        }
        return underlines;
    },
    provide(field: StateField<DecorationSet>) {
        return EditorView.decorations.from(field);
    }
})

// Type for a coq error range.
export type CoqErrorRange = {
    from: number;
    to: number;
}

// Type for a coq error range with error message and severity level.
export type CoqErrorRangeWithOptions = {
    from: number;
    to: number;
    message: string;
    severity: number;
}

/**
 * Add an effect for adding the state field if it is not present.
 * @param view The editor view.
 * @returns `null` when this is not necessary or an `StateEffect` when it is.
 */
function addStateFieldIfNotPresent(view: EditorView): null | StateEffect<unknown> {
    // Check if the coqError state field is present in the view
    if (!view.state.field(coqErrorStateField, false)) {
        // If the statefield is not yet present return an StateEffect that will append the
        // statefield to the view.
        return StateEffect.appendConfig.of([coqErrorStateField]);
    }
    return null;
}

/**
 * Helper function to get the effects to dispatch
 * @param view The editor view.
 * @param effect The effect we want to dispatch.
 * @returns The `effects` to dispatch, includes the 'state field adding effect' when necessary.
 */
function getEffectsToDispatch(view: EditorView, effect: StateEffect<unknown>): StateEffect<unknown>[] {
    const potentialEffect = addStateFieldIfNotPresent(view);
    const effects: StateEffect<unknown>[] = 
        potentialEffect ? [potentialEffect, effect] : [effect];
    return effects;
}

/**
 * Add a coq error mark to the state field.
 * @param view The editor view.
 * @param range The range of the editor to add (`{from: number, to: number}`).
 */
export function addCoqErrorMark(view: EditorView, range: CoqErrorRange, message: string, severity: number) {
    const coqErrorEffect: StateEffect<unknown> = addCoqErrorTransactionEffect.of({
        from: range.from, to: range.to, message, severity
    });
    view.dispatch({effects: getEffectsToDispatch(view, coqErrorEffect)});
}

/**
 * Remove a coq error mark from the state field.
 * @param view The editor view.
 * @param range The range of the editor to remove (`{from: number, to: number}`).
 */
export function removeCoqErrorMark(view: EditorView, range: CoqErrorRange) {
    const coqErrorEffect: StateEffect<unknown> = removeCoqErrorTransactionEffect.of(range);
    view.dispatch({effects: getEffectsToDispatch(view, coqErrorEffect)});
}

/**
 * Clear all errors from the state field.
 * @param view The editor view.
 */
export function clearCoqErrorMarks(view: EditorView) {
    const coqErrorEffect = clearCoqErrorsTransactionEffect.of(null);
    view.dispatch({effects: getEffectsToDispatch(view, coqErrorEffect)});
}