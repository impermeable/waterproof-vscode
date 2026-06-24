import { EventEmitter } from "events";
import { describe, expect, it, jest } from "@jest/globals";

// LLM-generated tests. It is possible these encode existing faulty behaviours.

// ---------------------------------------------------------------------------
// Module mocks — must be declared before any import that touches them.
// ---------------------------------------------------------------------------

jest.mock("vscode", () => ({
    Uri: {
        parse: jest.fn((s: string) => ({ toString: () => s })),
    },
    window: {
        showErrorMessage: jest.fn(),
        createStatusBarItem: jest.fn(() => ({
            show: jest.fn(),
            hide: jest.fn(),
            dispose: jest.fn(),
            text: "",
        })),
        createOutputChannel: jest.fn(() => ({
            appendLine: jest.fn(),
            dispose: jest.fn(),
        })),
    },
    StatusBarAlignment: { Left: 1, Right: 2 },
    workspace: {
        getConfiguration: jest.fn(() => ({ get: jest.fn() })),
    },
}), { virtual: true });

import { Message, MessageType } from "../../shared";
import { WebviewManager, WebviewManagerEvents } from "../../src/webviewManager";
import { WebviewEvents } from "../../src/webviews/waterproofPanel";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Minimal mock of a TextDocument with a controllable `positionAt`. */
function createMockDocument(uri = "file:///test.lean") {
    return {
        uri: { toString: () => uri },
        positionAt: jest.fn((offset: number) => ({
            line: Math.floor(offset / 100),
            character: offset % 100,
        })),
    };
}

/**
 * Minimal mock of a WaterproofWebview.
 *
 * It is an EventEmitter (so the manager can subscribe) and exposes the two
 * properties that `onProseMessage` reads: `document` and `documentIsUpToDate`.
 */
function createMockWebview(
    document: ReturnType<typeof createMockDocument>,
    opts: { documentIsUpToDate?: boolean } = {},
) {
    const webview = new EventEmitter() as EventEmitter & {
        document: ReturnType<typeof createMockDocument>;
        documentIsUpToDate: boolean;
        postMessage: jest.Mock;
    };
    webview.document = document;
    webview.documentIsUpToDate = opts.documentIsUpToDate ?? true;
    webview.postMessage = jest.fn();
    return webview;
}

/** Wire a mock webview into a fresh WebviewManager and return both. */
function setup(opts: { documentIsUpToDate?: boolean } = {}) {
    const document = createMockDocument();
    const webview = createMockWebview(document, opts);
    const manager = new WebviewManager();
    // Allowing any in order not need a big mock
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    manager.addWaterproofWebview(webview as any);
    return { manager, webview, document };
}

/** Emit a message as if it came from the ProseMirror editor. */
function sendMessage(
    webview: ReturnType<typeof createMockWebview>,
    message: Message,
) {
    webview.emit(WebviewEvents.message, message);
}

/** Collect all emissions of `event` on `emitter` into an array. */
function collectEvents(emitter: EventEmitter, event: string) {
    const collected: unknown[][] = [];
    emitter.on(event, (...args: unknown[]) => collected.push(args));
    return collected;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe("WebviewManager · onProseMessage", () => {

    // -- response -----------------------------------------------------------

    describe("MessageType.response", () => {
        it("invokes the stored callback matching the requestId", () => {
            const { manager, webview, document } = setup();

            const promise = manager.postMessageWithResponse(
                document.uri.toString(),
                { type: MessageType.editorReady } as Message,
            );

            sendMessage(webview, {
                type: MessageType.response,
                requestId: 1,
                body: "result-payload",
            } as unknown as Message);

            return expect(promise).resolves.toBe("result-payload");
        });

        it("logs an error when requestId is missing", () => {
            const { webview } = setup();
            const spy = jest.spyOn(console, "error").mockImplementation(() => {});

            sendMessage(webview, {
                type: MessageType.response,
                body: "orphan",
            } as unknown as Message);

            expect(spy).toHaveBeenCalledWith(
                expect.stringContaining("without a requestId"),
                expect.anything(),
            );
            spy.mockRestore();
        });
    });

    // -- editorReady --------------------------------------------------------

    describe("MessageType.editorReady", () => {
        it("emits WebviewManagerEvents.editorReady with the document", () => {
            const { manager, webview, document } = setup();
            const events = collectEvents(manager, WebviewManagerEvents.editorReady);

            sendMessage(webview, { type: MessageType.editorReady } as Message);

            expect(events).toHaveLength(1);
            expect(events[0][0]).toBe(document);
        });
    });

    // -- cursorChange -------------------------------------------------------

    describe("MessageType.cursorChange", () => {
        it("converts offset and emits immediately when document is up-to-date", () => {
            const { manager, webview, document } = setup({ documentIsUpToDate: true });
            const events = collectEvents(manager, WebviewManagerEvents.cursorChange);

            sendMessage(webview, { type: MessageType.cursorChange, body: 250 } as unknown as Message);

            expect(document.positionAt).toHaveBeenCalledWith(250);
            expect(events).toHaveLength(1);
            const [emittedDoc, emittedPos] = events[0];
            expect(emittedDoc).toBe(document);
            expect(emittedPos).toEqual({ line: 2, character: 50 });
        });

        it("defers positionAt and emit until finishUpdate when document is stale", () => {
            const { manager, webview, document } = setup({ documentIsUpToDate: false });
            const events = collectEvents(manager, WebviewManagerEvents.cursorChange);

            sendMessage(webview, { type: MessageType.cursorChange, body: 250 } as unknown as Message);

            // Nothing emitted yet – document was stale.
            expect(events).toHaveLength(0);
            expect(document.positionAt).not.toHaveBeenCalled();

            // Simulate the document update completing.
            webview.emit(WebviewEvents.finishUpdate);

            expect(document.positionAt).toHaveBeenCalledWith(250);
            expect(events).toHaveLength(1);
            expect(events[0][1]).toEqual({ line: 2, character: 50 });
        });

        it("uses the updated document for positionAt, not the stale one", () => {
            // Regression test for a bug that was here
            const { manager, webview, document } = setup({ documentIsUpToDate: false });
            const events = collectEvents(manager, WebviewManagerEvents.cursorChange);

            // Before update: offset 250 maps to line 3 (stale document).
            // After update:  offset 250 maps to line 2 (correct).
            let updated = false;
            document.positionAt.mockImplementation((offset: number) =>
                updated
                    ? { line: 2, character: offset % 100 }
                    : { line: 3, character: offset % 100 }
            );

            sendMessage(webview, { type: MessageType.cursorChange, body: 250 } as unknown as Message);

            // Simulate the document content changing.
            updated = true;
            webview.emit(WebviewEvents.finishUpdate);

            // Must see the post-update position, not the stale one.
            expect(events[0][1]).toEqual({ line: 2, character: 50 });
        });

        it("registers only one finishUpdate listener at a time", () => {
            const { manager, webview, document } = setup({ documentIsUpToDate: false });
            const events = collectEvents(manager, WebviewManagerEvents.cursorChange);

            sendMessage(webview, { type: MessageType.cursorChange, body: 100 } as unknown as Message);
            sendMessage(webview, { type: MessageType.cursorChange, body: 200 } as unknown as Message);

            // Only one listener registered; the second is dropped.
            expect(webview.listenerCount(WebviewEvents.finishUpdate)).toBe(1);

            webview.emit(WebviewEvents.finishUpdate);

            // Only the first cursor change fires.
            expect(events).toHaveLength(1);
            expect(document.positionAt).toHaveBeenCalledWith(100);
        });

        it("does nothing when the webview has been disposed", () => {
            const { manager, webview } = setup();

            // Remove the webview from the internal map by simulating dispose.
            webview.emit(WebviewEvents.dispose);

            const events = collectEvents(manager, WebviewManagerEvents.cursorChange);
            sendMessage(webview, { type: MessageType.cursorChange, body: 50 } as unknown as Message);

            expect(events).toHaveLength(0);
        });
    });

    // -- applyStepError -----------------------------------------------------

    describe("MessageType.applyStepError", () => {
        it("shows an error message to the user", async () => {
            const { webview } = setup();
            const { window } = await import("vscode");

            sendMessage(webview, {
                type: MessageType.applyStepError,
                body: "something broke",
            } as unknown as Message);

            expect(window.showErrorMessage).toHaveBeenCalledWith(
                expect.stringContaining("something broke"),
            );
        });
    });

    // -- command (Help) -----------------------------------------------------

    describe("MessageType.command", () => {
        it("forwards createHelp and then Help. to the goals tool panel", () => {
            jest.useFakeTimers();
            const { manager, webview } = setup();
            const events = collectEvents(manager, WebviewManagerEvents.command);

            sendMessage(webview, {
                type: MessageType.command,
                body: { command: "anything" },
            } as unknown as Message);

            // First call is synchronous: createHelp
            expect(events).toHaveLength(1);
            expect(events[0][1]).toBe("createHelp");

            // Second call fires after 250ms: "Help."
            jest.advanceTimersByTime(250);
            expect(events).toHaveLength(2);
            expect(events[1][1]).toBe("Help.");

            jest.useRealTimers();
        });
    });

    // -- viewportHint -------------------------------------------------------

    describe("MessageType.viewportHint", () => {
        it("emits viewportHint with document, start and end", () => {
            const { manager, webview, document } = setup();
            const events = collectEvents(manager, WebviewManagerEvents.viewportHint);

            sendMessage(webview, {
                type: MessageType.viewportHint,
                body: { start: 10, end: 50 },
            } as unknown as Message);

            expect(events).toHaveLength(1);
            expect(events[0][0]).toEqual({ document, start: 10, end: 50 });
        });
    });

    // -- default (unrecognized) ---------------------------------------------

    describe("unrecognized message type", () => {
        it("logs a console error", () => {
            const { webview } = setup();
            const spy = jest.spyOn(console, "error").mockImplementation(() => {});

            sendMessage(webview, { type: 99999, body: null } as unknown as Message);

            expect(spy).toHaveBeenCalledWith(
                expect.stringContaining("Unrecognized message type"),
            );
            spy.mockRestore();
        });
    });
});
