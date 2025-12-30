export type SimpleProgressInfo = {
    /** Range for which the processing info was reported. */
    range: {
        start: { line: number, character: number },
        end: { line: number, character: number },
    };
    /** Kind of progress that was reported. */
    kind?: CoqFileProgressKind;
}

export type SimpleProgressParams = {
    numberOfLines: number;
    progress: SimpleProgressInfo[];
}

export enum CoqFileProgressKind {
    Processing = 1,
    FatalError
}
