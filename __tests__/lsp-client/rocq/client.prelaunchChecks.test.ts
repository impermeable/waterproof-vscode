import { extensions } from "vscode";
import { RocqLspClient } from "../../../src/lsp-client/rocq/client";
import type { LanguageClientProvider } from "../../../src/lsp-client/clientTypes";
import type { ExtensionContext, OutputChannel } from "vscode";
import { makeClientDouble } from "../../__helpers__/lsp-client-mocks";
import type { mocks as MockFactories } from "../../__helpers__/lsp-client-mocks";

function lspMocks(): typeof MockFactories { return require("../../__helpers__/lsp-client-mocks").mocks; } // eslint-disable-line @typescript-eslint/no-require-imports

jest.mock("vscode", () => ({
    ...lspMocks().vscode(),
    extensions: { getExtension: jest.fn() },
}), { virtual: true });

jest.mock("vscode-languageclient",          () => lspMocks().languageClient(),      { virtual: true });
jest.mock("vscode-languageserver-types",    () => lspMocks().languageServerTypes(), { virtual: true });
jest.mock("../../../shared",                () => lspMocks().shared(),               { virtual: true });
jest.mock("../../../lib/types",             () => ({ RocqServerStatusToServerStatus: jest.fn() }), { virtual: true });
jest.mock("../../../src/helpers",           () => ({
    ...lspMocks().helpers(),
    WaterproofPackageJSON: { requiredCoqLspVersion: jest.fn(), requiredCoqWaterproofVersion: jest.fn() },
}));
jest.mock("../../../src/version-checker/version-checker", () => ({
    VersionChecker: jest.fn().mockImplementation(() => ({
        prelaunchChecks: jest.fn(() => Promise.resolve(false)),
        run: jest.fn(),
    })),
}));
jest.mock("../sentenceManager",             () => lspMocks().sentenceManager(),      { virtual: true });
jest.mock("../clientTypes",                 () => ({}),                               { virtual: true });
jest.mock("../requestTypes",                () => lspMocks().requestTypes(),           { virtual: true });
jest.mock("../qedStatus",                   () => ({ findOccurrences: jest.fn(), areInputAreasValid: jest.fn() }), { virtual: true });
jest.mock("./requestTypes",                 () => ({
    coqFileProgressNotificationType:     "$/coq/fileProgress",
    coqGoalRequestType:                  "$/coq/getGoals",
    coqServerStatusNotificationType:     "$/coq/serverStatus",
    executionInformationNotificationType: "$/coq/executionInfo",
}), { virtual: true });
jest.mock("@impermeable/waterproof-editor", () => lspMocks().waterproofEditor(),     { virtual: true });
jest.mock("@leanprover/infoview-api",       () => ({}),                               { virtual: true });

function makeClient() {
    return new RocqLspClient(
        jest.fn(() => makeClientDouble()) as LanguageClientProvider,
        { appendLine: jest.fn() } as unknown as OutputChannel,
        {} as unknown as ExtensionContext,
    );
}

beforeEach(() => {
    jest.clearAllMocks();
    jest.mocked(extensions.getExtension).mockReturnValue(undefined);
});

describe("RocqLspClient.prelaunchChecks — conflicting extension guard", () => {
    it("skips the Rocq client when Coq LSP is installed", async () => {
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "ejgallego.coq-lsp" ? { id } as never : undefined
        );

        expect(await makeClient().prelaunchChecks()).toEqual([]);
    });

    it("skips the Rocq client when VSCoq is installed", async () => {
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "maximedenes.vscoq" ? { id } as never : undefined
        );

        expect(await makeClient().prelaunchChecks()).toEqual([]);
    });

    it("logs that a conflicting Rocq extension was found", async () => {
        const { WaterproofLogger: wpl } = await import("../../../src/helpers");
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "ejgallego.coq-lsp" ? { id } as never : undefined
        );

        await makeClient().prelaunchChecks();

        expect(wpl.log).toHaveBeenCalledWith(expect.stringContaining("Conflicting Rocq extension detected"));
    });

    it("proceeds to the version check when no conflicting extension is installed", async () => {
        const { VersionChecker } = await import("../../../src/version-checker/version-checker");

        await makeClient().prelaunchChecks();

        expect(VersionChecker).toHaveBeenCalled();
    });

    it("does not skip startup when only the Lean 4 extension is installed", async () => {
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "leanprover.lean4" ? { id } as never : undefined
        );
        const { VersionChecker } = await import("../../../src/version-checker/version-checker");

        await makeClient().prelaunchChecks();

        expect(VersionChecker).toHaveBeenCalled();
    });
});
