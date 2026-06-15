import { extensions } from "vscode";
import { LeanLspClient } from "../../../src/lsp-client/lean/client";
import { WaterproofConfigHelper, WaterproofLogger as wpl } from "../../../src/helpers";
import type { LanguageClientProvider } from "../../../src/lsp-client/clientTypes";
import type { OutputChannel } from "vscode";
import { makeClientDouble } from "../../__helpers__/lsp-client-mocks";
import type { mocks as MockFactories } from "../../__helpers__/lsp-client-mocks";

function lspMocks(): typeof MockFactories { return require("../../__helpers__/lsp-client-mocks").mocks; } // eslint-disable-line @typescript-eslint/no-require-imports

jest.mock("vscode", () => ({
    ...lspMocks().vscode(),
    extensions: { getExtension: jest.fn() },
}), { virtual: true });
jest.mock("../../../src/lsp-client/lean/converter", () => ({
    patchDiagnosticConverters: jest.fn(),
}), { virtual: true });
jest.mock("vscode-languageclient",          () => lspMocks().languageClient(),      { virtual: true });
jest.mock("vscode-languageserver-types",    () => lspMocks().languageServerTypes(), { virtual: true });
jest.mock("../../../shared",                () => lspMocks().shared(),               { virtual: true });
jest.mock("../../../lib/types",             () => ({}),                              { virtual: true });
jest.mock("../../../src/helpers",           () => lspMocks().helpers());
jest.mock("../sentenceManager",             () => lspMocks().sentenceManager(),      { virtual: true });
jest.mock("../clientTypes",                 () => ({}),                              { virtual: true });
jest.mock("../requestTypes",                () => lspMocks().requestTypes(),          { virtual: true });
jest.mock("./requestTypes",                 () => ({
    leanFileProgressNotificationType: "$/lean/fileProgress",
    leanGoalRequestType:              "$/lean/plainGoal",
}), { virtual: true });
jest.mock("@impermeable/waterproof-editor", () => lspMocks().waterproofEditor(),    { virtual: true });
jest.mock("@leanprover/infoview-api",       () => ({}),                              { virtual: true });

function makeClient() {
    return new LeanLspClient(
        jest.fn(() => makeClientDouble()) as LanguageClientProvider,
        { appendLine: jest.fn() } as unknown as OutputChannel,
    );
}

beforeEach(() => {
    jest.clearAllMocks();
    jest.mocked(extensions.getExtension).mockReturnValue(undefined);
});

describe("LeanLspClient.prelaunchChecks - lean4 guard", () => {
    it("skips the Lean client when the official Lean 4 extension is active", async () => {
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "leanprover.lean4" ? { id } as never : undefined
        );

        const result = await makeClient().prelaunchChecks();

        expect(result).toEqual([]);
    });

    it("logs that the official Lean 4 extension was detected", async () => {
        jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
            id === "leanprover.lean4" ? { id } as never : undefined
        );

        await makeClient().prelaunchChecks();

        expect(wpl.log).toHaveBeenCalledWith(expect.stringContaining("Lean 4 extension detected"));
    });

    it("skips the Lean client when no lake path is configured", async () => {
        jest.mocked(WaterproofConfigHelper.get).mockReturnValue("");

        const result = await makeClient().prelaunchChecks();

        expect(result).toEqual([]);
    });

    it("logs that the lake path is missing when no path is configured", async () => {
        jest.mocked(WaterproofConfigHelper.get).mockReturnValue(false);

        await makeClient().prelaunchChecks();

        expect(wpl.log).toHaveBeenCalledWith(expect.stringContaining("lakePath is empty"));
    });
});
