import { window } from "vscode";

export function getNonInputRegions(doc: string) {
        
    // get all input areas: 
    const inputOpenTags = Array.from(doc.matchAll(/<input-area>/g));
    const inputCloseTags = Array.from(doc.matchAll(/<\/input-area>/g));

    const fromString = (input: string) => {
        return input === "<input-area>" ? "open" : "close";
    }

    const allTags = [...inputOpenTags, ...inputCloseTags].map((value) => {
        // open     -> consider position at the start of tag. 
        // close    -> consider position at the end of tag.
        const type = fromString(value[0]);
        switch (type) {
            case "open": 
                return {position: value.index as number + value[0].length, type}
            case "close": 
                return {position: value.index as number, type}
        }
        

    }).sort((a, b) => a.position - b.position);


    const pairsCombined = Array.from(
        {length:allTags.length/2}, 
        (_,i) => {
            const open = allTags[2*i];
            const close = allTags[2*i + 1];
            // const content = docOnDisk.substring(open.position, close.position);
            return {open, close};
        }
    );


    const outsideInputAreaRegions = Array.from({length: pairsCombined.length + 1}, (_, i) => {
        if (i == 0) {
            // special case
            return { from: 0, to: pairsCombined[i].open.position }
        } else if (i == pairsCombined.length) {
            return { from: pairsCombined[i-1].close.position, to: doc.length }
        } else {
            return { from: pairsCombined[i-1].close.position, to: pairsCombined[i].open.position }
        }
    }).map(value => {
        return {...value, content: doc.substring(value.from, value.to)}
    });

    return outsideInputAreaRegions;
}

const RESTORE = "Restore";

export const showRestoreMessage = (cbOnRestore: () => void) => {
    window.showErrorMessage("Waterproof: The content outside of the input areas changed, this is not supposed to happen! Click the button below to restore.", RESTORE).then(restoreHandler(cbOnRestore));
}

const restoreHandler = (cbOnRestore: () => void) => {
    return (value: typeof RESTORE | undefined) => {
        if (value == RESTORE) cbOnRestore();
    }
}