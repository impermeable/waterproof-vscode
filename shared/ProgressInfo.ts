export type SimpleProgressInfo = {
    /** Range for which the processing info was reported. */
    range: {
        start: { line: number, character: number },
        end: { line: number, character: number },
    };
    /** Kind of progress that was reported. */
    kind?: FileProgressKind;
}

export type SimpleProgressParams = {
    numberOfLines: number;
    progress: SimpleProgressInfo[];
}


export enum FileProgressKind {
    Processing = 1,
    FatalError = 2
}
