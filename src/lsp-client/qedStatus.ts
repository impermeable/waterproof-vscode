// TODO: only consider Markdown parts
export function findOccurrences(substr: string, str: string): number[] {
    const indices: number[] = [];
    const substrLen = substr.length;
    for (let i = 0; (i = str.indexOf(substr, i)) >= 0; i += substrLen) indices.push(i);
    return indices;  // sorted
}

/** Returns whether input areas are not interleaved. */
export function areInputAreasValid(open: number[], close: number[]): boolean {
    if (open.length !== close.length) return false;
    if (open.length && open[0] > close[0]) return false;  // "base" case of loop below
    for (let i = 1; i < open.length; i++)
        if (close[i-1] > open[i] || open[i] > close[i])
            return false;
    return true;
}
