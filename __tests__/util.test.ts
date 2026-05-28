import { extensions, window, workspace, commands, env } from "vscode";
import type { ExtensionContext } from "vscode";
import { checkConflictingExtensions } from "../src/util";

jest.mock("vscode", () => ({
    Uri: {
        joinPath: jest.fn((_base: unknown, ...segments: string[]) => ({
            fsPath: "/global-storage/" + segments.join("/"),
            toString: () => "file:///global-storage/" + segments.join("/"),
        })),
        parse: jest.fn((s: string) => ({ toString: () => s })),
    },
    extensions: {
        getExtension: jest.fn(),
        all: [],
    },
    window: {
        showWarningMessage:     jest.fn(),
        showInformationMessage: jest.fn(),
        showErrorMessage:       jest.fn(),
    },
    workspace: {
        fs: { writeFile: jest.fn() },
        getConfiguration: jest.fn(() => ({ get: jest.fn((_key: string, def?: unknown) => def) })),
    },
    commands: {
        executeCommand: jest.fn(),
    },
    env: {
        clipboard: { writeText: jest.fn() },
        openExternal: jest.fn(),
    },
}), { virtual: true });

jest.mock("../src/helpers", () => ({
    WaterproofConfigHelper: { get: jest.fn(() => false) },
    WaterproofLogger: { log: jest.fn(), debug: jest.fn() },
    WaterproofSetting: {},
    qualifiedSettingName: jest.fn((s: string) => s),
}));

function makeContext(): ExtensionContext {
    return { globalStorageUri: { fsPath: "/global-storage" } } as ExtensionContext;
}

function mockGetExtension(installedIds: string[]) {
    jest.mocked(extensions.getExtension).mockImplementation((id: string) =>
        installedIds.includes(id) ? { id } as never : undefined
    );
}

beforeEach(() => {
    jest.clearAllMocks();
    jest.requireMock("vscode").extensions.all = [];
});

describe("checkConflictingExtensions", () => {
    it("does nothing when no conflicting extensions are installed", async () => {
        mockGetExtension([]);
        await checkConflictingExtensions(makeContext());
        expect(window.showWarningMessage).not.toHaveBeenCalled();
    });

    it("shows warning with Lean 4 name when only lean4 is installed", async () => {
        mockGetExtension(["leanprover.lean4"]);
        jest.mocked(window.showWarningMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        expect(window.showWarningMessage).toHaveBeenCalledTimes(1);
        const [msg] = jest.mocked(window.showWarningMessage).mock.calls[0];
        expect(msg).toContain("Lean 4");
        expect(msg).not.toContain("Coq LSP");
        expect(msg).not.toContain("VSCoq");
    });

    it("shows warning with Coq LSP name when only coq-lsp is installed", async () => {
        mockGetExtension(["ejgallego.coq-lsp"]);
        jest.mocked(window.showWarningMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        const [msg] = jest.mocked(window.showWarningMessage).mock.calls[0];
        expect(msg).toContain("Coq LSP");
    });

    it("shows warning listing all conflicting extensions when multiple are installed", async () => {
        mockGetExtension(["leanprover.lean4", "ejgallego.coq-lsp", "maximedenes.vscoq"]);
        jest.mocked(window.showWarningMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        const [msg] = jest.mocked(window.showWarningMessage).mock.calls[0];
        expect(msg).toContain("Lean 4");
        expect(msg).toContain("Coq LSP");
        expect(msg).toContain("VSCoq");
    });

    it("warning message offers 'Set up Waterproof Profile' and 'Dismiss' actions", async () => {
        mockGetExtension(["leanprover.lean4"]);
        jest.mocked(window.showWarningMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        const args = jest.mocked(window.showWarningMessage).mock.calls[0];
        expect(args).toContain("Set up Waterproof Profile");
        expect(args).toContain("Dismiss");
    });

    it("does not start profile setup when user dismisses the warning", async () => {
        mockGetExtension(["leanprover.lean4"]);
        jest.mocked(window.showWarningMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        expect(workspace.fs.writeFile).not.toHaveBeenCalled();
    });

    it("does not start profile setup when user clicks Dismiss", async () => {
        mockGetExtension(["leanprover.lean4"]);
        (window.showWarningMessage as jest.Mock).mockResolvedValue("Dismiss");

        await checkConflictingExtensions(makeContext());

        expect(workspace.fs.writeFile).not.toHaveBeenCalled();
    });

    it("starts profile setup when user clicks 'Set up Waterproof Profile'", async () => {
        mockGetExtension(["leanprover.lean4"]);
        (window.showWarningMessage as jest.Mock).mockResolvedValue("Set up Waterproof Profile");
        jest.mocked(workspace.fs.writeFile).mockResolvedValue(undefined);
        jest.mocked(commands.executeCommand).mockResolvedValue(undefined);
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        expect(workspace.fs.writeFile).toHaveBeenCalled();
    });
});

describe("setupWaterproofProfile (triggered via checkConflictingExtensions)", () => {
    type ExtEntry = { id: string; packageJSON: { isBuiltin: boolean; version: string } };

    async function triggerSetup(installedConflicting: string[], allExtensions: ExtEntry[] = [], installedAll?: string[]) {
        mockGetExtension(installedAll ?? installedConflicting);
        jest.requireMock("vscode").extensions.all = allExtensions;
        (window.showWarningMessage as jest.Mock).mockResolvedValue("Set up Waterproof Profile");
        jest.mocked(workspace.fs.writeFile).mockResolvedValue(undefined);
        jest.mocked(commands.executeCommand).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());
    }

    function readProfileExtensions(data: Uint8Array): { identifier: { id: string }; disabled?: boolean }[] {
        return JSON.parse(JSON.parse(new TextDecoder().decode(data)).extensions);
    }

    it("writes a .code-profile file to globalStorageUri", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"]);

        expect(workspace.fs.writeFile).toHaveBeenCalledTimes(1);
        const [uri] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        expect(uri.fsPath).toContain("waterproof.code-profile");
    });

    it("profile JSON contains a 'Waterproof' name field", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        expect(JSON.parse(new TextDecoder().decode(data)).name).toBe("Waterproof");
    });

    it("profile does not include conflicting extensions", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4", "ejgallego.coq-lsp"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);

        expect(ids).not.toContain("leanprover.lean4");
        expect(ids).not.toContain("ejgallego.coq-lsp");
    });

    it("includes waterproof extension when installed", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"], [], ["leanprover.lean4", "waterproof-tue.waterproof"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);
        expect(ids).toContain("waterproof-tue.waterproof");
    });

    it("includes waterproof-river when installed", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"], [], ["leanprover.lean4", "waterproof-tue.waterproof", "waterproof-tue.waterproof-river"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);
        expect(ids).toContain("waterproof-tue.waterproof-river");
    });

    it("omits waterproof-river when not installed", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        mockGetExtension(["leanprover.lean4", "waterproof-tue.waterproof"]);

        await triggerSetup(["leanprover.lean4"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);
        expect(ids).not.toContain("waterproof-tue.waterproof-river");
    });

    it("does not include arbitrary user extensions", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        mockGetExtension(["leanprover.lean4", "waterproof-tue.waterproof"]);
        jest.requireMock("vscode").extensions.all = [
            { id: "publisher.some-other-ext", packageJSON: { isBuiltin: false, version: "1.0.0" } },
        ];

        await triggerSetup(["leanprover.lean4"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);
        expect(ids).not.toContain("publisher.some-other-ext");
    });

    it("conflicting extension is not included in the profile", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"], [], ["leanprover.lean4", "waterproof-tue.waterproof"]);

        const [, data] = jest.mocked(workspace.fs.writeFile).mock.calls[0];
        const ids = readProfileExtensions(data).map(e => e.identifier.id);
        expect(ids).not.toContain("leanprover.lean4");
    });

    it("executes 'workbench.profiles.actions.manageProfiles' after writing the file", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"]);

        expect(commands.executeCommand).toHaveBeenCalledWith("workbench.profiles.actions.manageProfiles");
    });

    it("shows an info message containing the profile file path", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"]);

        expect(window.showInformationMessage).toHaveBeenCalledTimes(1);
        const [msg] = jest.mocked(window.showInformationMessage).mock.calls[0];
        expect(msg).toContain("waterproof.code-profile");
    });

    it("copies the profile path to clipboard when user clicks 'Copy Path'", async () => {
        (window.showInformationMessage as jest.Mock).mockResolvedValue("Copy Path");
        await triggerSetup(["leanprover.lean4"]);

        expect(env.clipboard.writeText).toHaveBeenCalledTimes(1);
        const [text] = jest.mocked(env.clipboard.writeText).mock.calls[0];
        expect(text).toContain("waterproof.code-profile");
    });

    it("does not copy to clipboard when user dismisses the info message", async () => {
        jest.mocked(window.showInformationMessage).mockResolvedValue(undefined);
        await triggerSetup(["leanprover.lean4"]);

        expect(env.clipboard.writeText).not.toHaveBeenCalled();
    });

    it("shows an error message when file write fails", async () => {
        mockGetExtension(["leanprover.lean4"]);
        (window.showWarningMessage as jest.Mock).mockResolvedValue("Set up Waterproof Profile");
        jest.mocked(workspace.fs.writeFile).mockRejectedValue(new Error("disk full"));
        jest.mocked(window.showErrorMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        expect(window.showErrorMessage).toHaveBeenCalledTimes(1);
        expect(window.showInformationMessage).not.toHaveBeenCalled();
    });

    it("does not show an info message when file write fails", async () => {
        mockGetExtension(["leanprover.lean4"]);
        (window.showWarningMessage as jest.Mock).mockResolvedValue("Set up Waterproof Profile");
        jest.mocked(workspace.fs.writeFile).mockRejectedValue(new Error("disk full"));
        jest.mocked(window.showErrorMessage).mockResolvedValue(undefined);

        await checkConflictingExtensions(makeContext());

        expect(window.showInformationMessage).not.toHaveBeenCalled();
    });
});
