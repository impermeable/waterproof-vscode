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

test("checkPrePost #1", () => {
    const pm = new PostManager();
    expect(checkPrePost("```coq\nLemma.\n```", (msg) => pm.post(msg))).toBe("\n```coq\nLemma.\n```\n");
    expect(pm.storage).toStrictEqual<Array<Message>>([{
        type: MessageType.docChange, 
        body: {
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
    }]);
});

test("checkPrePost #2", () => {
    const pm = new PostManager();
    expect(checkPrePost("```coq\nLemma.\n```\n# Some markdown", (msg) => pm.post(msg))).toBe("\n```coq\nLemma.\n```\n# Some markdown");
    expect(pm.storage).toStrictEqual<Array<Message>>([
        {
            type: MessageType.docChange,
            body: {
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
        }
    ]);
});

test("checkPrePost #3", () => {
    const pm = new PostManager();
    expect(checkPrePost("# Some markdown\n```coq\nLemma.\n```", (msg) => pm.post(msg))).toBe("# Some markdown\n```coq\nLemma.\n```\n");
    expect(pm.storage).toStrictEqual<Array<Message>>([
        {
            type: MessageType.docChange,
            body: {
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
        }
    ]);
});

test("checkPrePost #4", () => {
    const pm = new PostManager();
    expect(checkPrePost("# Some markdown\n```coq\nLemma.\n```\n# Some markdown", (msg) => pm.post(msg))).toBe("# Some markdown\n```coq\nLemma.\n```\n# Some markdown");
    expect(pm.storage).toStrictEqual<Array<Message>>([]);
});