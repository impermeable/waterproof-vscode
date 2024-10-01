import {ExternalTokenizer} from "@lezer/lr"

export const TakeInput = new ExternalTokenizer((input, stack) => {
    let pos = input.pos;

    // Skip the "Take"
    if (input.read(pos, pos+4) === "Take") {
        pos += 4;
    } else {
        return;
    }

    // Capture until the colon or newline
    const start = pos;
    while (pos < input.end && input.read(pos, pos+1) !== ":" && input.read(pos, pos+1) != "\n") {
        pos++;
    }

    // Debugging
    console.log("Captured token:");
    console.log(input.read(start, pos));
    console.log(pos);
    console.log(input.end);
    console.log();

    if (pos < input.end) {
        input.acceptToken(TakeInput, pos);
    }
}, { contextual: true });
