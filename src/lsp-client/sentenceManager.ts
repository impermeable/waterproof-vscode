import { Position } from "vscode";
import { IFileProgressComponent } from "../components";
import { CoqFileProgressParams } from "./requestTypes";

// TODO: Figure out if this is unused, and if yes, delete file and usages.

export class SentenceManager implements IFileProgressComponent {

    /**
     * The positions in the current document where a Coq sentence ends.
     * Invariant: This array is sorted.
     * TODO: clear when switching document
     */
    private readonly sentenceEndPositions: Position[] = [];

    /**
     * Computes the number of elements in `sentenceEndPositions` that come strictly before
     * `position`, i.e., the index of `position` (if it were in the array).
     */
    private getRank(position: Position): number {
        // special case: check if after last, since it occurs most often ==> efficient
        let r = this.sentenceEndPositions.length;
        if (r === 0) return 0;
        const last = this.sentenceEndPositions[r-1];
        if (position.isAfter(last)) return r;

        // binary search
        let l = 0;
        while (l < r) {
            const m = Math.floor((l + r) / 2);
            if (this.sentenceEndPositions[m].isBefore(position))
                l = m + 1;
            else
                r = m;
        }
        return l;
    }

    private removeAfterOrEqual(position: Position): void {
        const i = this.getRank(position);
        this.sentenceEndPositions.splice(i, this.sentenceEndPositions.length - i);
    }

    onProgress(params: CoqFileProgressParams): void {
        // get position from each processed range (always just one? we assume it's sorted)
        // end position is always end of document, so useless
        const positions = params.processing.map(info => info.range.start);
        if (positions.length === 0) return;

        // remove (potentially) outdated positions
        this.removeAfterOrEqual(positions[0]);

        // add new positions
        this.sentenceEndPositions.push(...positions);
    }

    /**
     * Returns the beginning position of the sentence in which `position` is located.
     * That is, the end position of the previous sentence.
     */
    getBeginningOfSentence(position: Position): Position | undefined {
        // FIXME: This is really just a hack to get things to work for now.
        const n = this.sentenceEndPositions.length;
        if (n === 0) return undefined;
        const i = this.getRank(position) - 1;
        const sentenceEndPosition = this.sentenceEndPositions[i];
        if (this.sentenceEndPositions[i+1].isEqual(position)) {
            return this.sentenceEndPositions[i+1];
        } else {
            return sentenceEndPosition;
        }
        
    }

    /**
     * Returns the end position of the sentence in which `position` is located.
     * If `strict`, return `undefined` if no sentences are known or if `position` is after the last.
     * In the second case, if not `strict`, simply return the last sentence.
     */
    getEndOfSentence(position: Position, strict: boolean = false): Position | undefined {
        const n = this.sentenceEndPositions.length;
        if (n === 0) return undefined;
        const i = this.getRank(position);

        if (i === n)
            return strict ? undefined : this.sentenceEndPositions[n-1];
        else
            return this.sentenceEndPositions[i];
    }

    dispose() {}

}
