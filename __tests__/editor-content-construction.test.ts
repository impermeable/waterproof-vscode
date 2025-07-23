import { checkPrePost, fixLessThanBug } from "../editor/src/kroqed-editor/file-utils";
import { Message, MessageType } from "../shared";

class PostManager {
    public storage: Array<Message> = [];

    public post(msg: Message) {
        this.storage.push(msg);
    }
}

test("TEMP: Add space between '<' and characters following it #1", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("```coq\n10<z\n```", (msg) => pm.post(msg))).toBe("```coq\n10< z\n```");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange,
        body: {
            startInFile: 10,
            endInFile: 10,
            finalText: " ",
        }
    }]);
});

test("TEMP: Add space between '<' and characters following it #2", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("```coq\n10<:10\n```", (msg) => pm.post(msg))).toBe("```coq\n10<:10\n```");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Add space between '<' and characters following it #3", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("```coq\n10< test\n```", (msg) => pm.post(msg))).toBe("```coq\n10< test\n```");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Add space between '<' and characters following it #4", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("```coq\n10<10\n```", (msg) => pm.post(msg))).toBe("```coq\n10< 10\n```");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange, 
        body: {
            startInFile: 10,
            endInFile: 10, 
            finalText: " "
        }
    }]);
});

test("TEMP: Add space between '<' and characters following it #5", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("<input-area>\n10<z\n</input-area>", (msg) => pm.post(msg))).toBe("<input-area>\n10< z\n</input-area>");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange, 
        body: {
            startInFile: 16, 
            endInFile: 16, 
            finalText: " "
        }
    }]);
});

test("TEMP: Leave <hint> untouched", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("<hint>\n# Hint content\n</hint>", (msg) => pm.post(msg))).toBe("<hint>\n# Hint content\n</hint>");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Leave <input-area> untouched", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("<input-area>\n# input-area content\n</input-area>", (msg) => pm.post(msg))).toBe("<input-area>\n# input-area content\n</input-area>");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Leave <br> in markdown untouched", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("# Markdown\n<br>", (msg) => pm.post(msg))).toBe("# Markdown\n<br>");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Leave <br> in markdown untouched #2", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("# Markdown\n<br>\n10<z", (msg) => pm.post(msg))).toBe("# Markdown\n<br>\n10< z");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange,
        body: {
            startInFile: 19, 
            endInFile: 19, 
            finalText: " "
        }
    }]);
});

test("TEMP: Leave <hr> in markdown untouched", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("# Markdown\n<hr>", (msg) => pm.post(msg))).toBe("# Markdown\n<hr>");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});

test("TEMP: Leave <hr> in markdown untouched #2", () => {
    const pm = new PostManager();
    expect(fixLessThanBug("# Markdown\n<hr>\n10<z", (msg) => pm.post(msg))).toBe("# Markdown\n<hr>\n10< z");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange,
        body: {
            startInFile: 19, 
            endInFile: 19, 
            finalText: " "
        }
    }]);
});

test("checkPrePost #1", () => {
    expect(checkPrePost("```coq\nLemma.\n```"))
        .toStrictEqual({
            resultingDocument: "\n```coq\nLemma.\n```\n",
            documentChange: {
                firstEdit: {
                    startInFile: 0,
                    endInFile: 0,
                    finalText: "\n"
                },
                secondEdit: {
                    startInFile: 17,
                    endInFile: 17,
                    finalText: "\n"
                }
            }
        });
});

test("checkPrePost #2", () => {
    expect(checkPrePost("```coq\nLemma.\n```\n# Some markdown"))
        .toStrictEqual({
            resultingDocument: "\n```coq\nLemma.\n```\n# Some markdown",
            documentChange: {
                firstEdit: {
                    startInFile: 0,
                    endInFile: 0,
                    finalText: "\n"
                },
                secondEdit: {
                    startInFile: 33,
                    endInFile: 33,
                    finalText: ""
                }
            }
        });
});

test("checkPrePost #3", () => {
    expect(checkPrePost("# Some markdown\n```coq\nLemma.\n```"))
        .toStrictEqual({
            resultingDocument: "# Some markdown\n```coq\nLemma.\n```\n",
            documentChange: {
                firstEdit: {
                    startInFile: 0,
                    endInFile: 0,
                    finalText: ""
                },
                secondEdit: {
                    startInFile: 33,
                    endInFile: 33,
                    finalText: "\n"
                }
            }
        });
});

test("checkPrePost #4", () => {
    expect(checkPrePost("# Some markdown\n```coq\nLemma.\n```\n# Some markdown"))
        .toStrictEqual({
            resultingDocument: "# Some markdown\n```coq\nLemma.\n```\n# Some markdown",
            documentChange: undefined
        });
});