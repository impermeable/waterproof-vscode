import { Message, MessageType } from "../../shared";
import { handleEditorMessage, MessageHandlerEditor } from "../../editor/src/messageHandler";

function createEditorMock(): jest.Mocked<MessageHandlerEditor> {
    return {
        init: jest.fn(),
        insertSymbol: jest.fn(),
        handleSnippet: jest.fn(),
        replaceRange: jest.fn(),
        handleCompletions: jest.fn(),
        setInputAreaStatus: jest.fn(),
        setShowLineNumbers: jest.fn(),
        setShowMenuItems: jest.fn(),
        handleHistoryChange: jest.fn(),
        updateLockingState: jest.fn(),
        removeBusyIndicators: jest.fn(),
        reportProgress: jest.fn(),
        setBusyIndicator: jest.fn(),
        setActiveDiagnostics: jest.fn(),
        startSpinner: jest.fn(),
        stopSpinner: jest.fn(),
        updateNodeViewThemes: jest.fn(),
    };
}

describe("handleEditorMessage", () => {
    describe("insert", () => {
        it("calls handleSnippet for tactics type, not insertSymbol", () => {
            const editor = createEditorMock();
            const msg: Message = {
                type: MessageType.insert,
                body: { symbolUnicode: "intro", type: "tactics", time: 1 },
            };

            handleEditorMessage(editor, msg);

            expect(editor.handleSnippet).toHaveBeenCalledWith("intro");
            expect(editor.insertSymbol).not.toHaveBeenCalled();
        });

        it("calls insertSymbol for non-tactics type, not handleSnippet", () => {
            const editor = createEditorMock();
            const msg: Message = {
                type: MessageType.insert,
                body: { symbolUnicode: "∀", type: "symbol", time: 1 },
            };

            handleEditorMessage(editor, msg);

            expect(editor.insertSymbol).toHaveBeenCalledWith("∀");
            expect(editor.handleSnippet).not.toHaveBeenCalled();
        });

        it("aborts silently when tactics type has no symbolUnicode", () => {
            const editor = createEditorMock();
            const msg = {
                type: MessageType.insert,
                body: { symbolUnicode: undefined, type: "tactics", time: 1 },
            } as unknown as Message;

            handleEditorMessage(editor, msg);

            expect(editor.handleSnippet).not.toHaveBeenCalled();
            expect(editor.insertSymbol).not.toHaveBeenCalled();
        });
    });

    describe("progress", () => {
        it("clears busy indicators and reports 'File verified' when progress is empty", () => {
            const editor = createEditorMock();
            const numberOfLines = 12;
            const msg: Message = {
                type: MessageType.progress,
                body: { numberOfLines, progress: [] },
            };

            handleEditorMessage(editor, msg);

            expect(editor.removeBusyIndicators).toHaveBeenCalledTimes(1);
            expect(editor.reportProgress).toHaveBeenCalledWith(numberOfLines, numberOfLines, "File verified");
        });

        it("reports partial progress message when not yet on the last line", () => {
            const editor = createEditorMock();
            const msg: Message = {
                type: MessageType.progress,
                body: {
                    numberOfLines: 100,
                    progress: [{ range: { start: { line: 29, character: 0 }, end: { line: 29, character: 0 } } }],
                },
            };

            handleEditorMessage(editor, msg);

            expect(editor.reportProgress).toHaveBeenCalledWith(30, 100, expect.stringContaining("30"));
            expect(editor.removeBusyIndicators).not.toHaveBeenCalled();
        });
    });

    describe("serverStatus", () => {
        it("starts spinner when status is Busy", () => {
            const editor = createEditorMock();
            const msg: Message = {
                type: MessageType.serverStatus,
                body: { status: "Busy", metadata: "type-checking" },
            };

            handleEditorMessage(editor, msg);

            expect(editor.startSpinner).toHaveBeenCalledTimes(1);
            expect(editor.stopSpinner).not.toHaveBeenCalled();
        });

        it("stops spinner when status is not Busy", () => {
            const editor = createEditorMock();
            const msg: Message = {
                type: MessageType.serverStatus,
                body: { status: "Idle" },
            };

            handleEditorMessage(editor, msg);

            expect(editor.stopSpinner).toHaveBeenCalledTimes(1);
            expect(editor.startSpinner).not.toHaveBeenCalled();
        });
    });
});