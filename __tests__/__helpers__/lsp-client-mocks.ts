import type { LanguageClient } from "../../src/lsp-client/clientTypes";
import { createVscodeLspMock } from "./vscode-lsp-mock";

export const mocks = {
    vscode:              createVscodeLspMock,
    languageClient:      () => ({
        LogTraceNotification:  { type: "$/logTrace" },
        RequestType:           jest.fn().mockImplementation(() => ({})),
        NotificationType:      jest.fn().mockImplementation(() => ({})),
        DocumentSymbolRequest: { type: {} },
    }),
    languageServerTypes: () => ({
        VersionedTextDocumentIdentifier: { create: jest.fn((uri: string, v: number) => ({ uri, version: v })) },
    }),
    shared:              () => ({ MessageType: {}, FileProgressKind: { Processing: 1 } }),
    helpers:             () => ({
        WaterproofConfigHelper: { get: jest.fn(() => false) },
        WaterproofLogger:       { log: jest.fn(), debug: jest.fn() },
        WaterproofSetting:      {},
        qualifiedSettingName:   jest.fn((s: string) => s),
    }),
    sentenceManager:     () => ({ SentenceManager: class { onProgress() {} dispose() {} } }),
    requestTypes:        () => ({ convertToSimple: jest.fn() }),
    waterproofEditor:    () => ({ InputAreaStatus: { Correct: "Correct", Incorrect: "Incorrect", Invalid: "Invalid" } }),
};

export function makeClientDouble(): LanguageClient {
    return {
        isRunning:              jest.fn(() => true),
        start:                  jest.fn(() => Promise.resolve()),
        dispose:                jest.fn(() => Promise.resolve()),
        onNotification:         jest.fn(() => ({ dispose: jest.fn() })),
        sendRequest:            jest.fn(),
        middleware:             { handleDiagnostics: undefined },
        protocol2CodeConverter: { asRange: (r: unknown) => r },
        code2ProtocolConverter: { asUri: (u: { toString(): string }) => u.toString(), asDiagnostic: (d: unknown) => d },
    } as unknown as LanguageClient;
}
