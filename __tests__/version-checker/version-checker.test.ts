import { exec } from "child_process";
import type { ExtensionContext } from "vscode";
import { VersionChecker } from "../../src/version-checker/version-checker";

jest.mock("child_process", () => ({ exec: jest.fn() }));

jest.mock(
  "vscode",
  () => ({
    Uri: { parse: jest.fn() },
    commands: { executeCommand: jest.fn() },
    env: { openExternal: jest.fn(), remoteName: undefined },
    window: {
      showInformationMessage: jest.fn(() => Promise.resolve(undefined)),
      showErrorMessage: jest.fn(() => Promise.resolve(undefined)),
    },
  }),
  { virtual: true },
);

jest.mock("../../src/helpers", () => ({
  WaterproofConfigHelper: { get: jest.fn(() => "/opt/wp/bin/coq-lsp") },
  WaterproofSetting: { Path: "path" },
  WaterproofFileUtil: {
    getDirectory: (p: string) => p.substring(0, p.lastIndexOf("/")),
    join: (...parts: string[]) => parts.join("/"),
  },
  WaterproofPackageJSON: {
    defaultCoqLspPathWindows: jest.fn(() => "C:/default/coq-lsp.exe"),
  },
  WaterproofLogger: { log: jest.fn(), debug: jest.fn() },
}));

type ExecCallback = (err: Error | null, stdout: string, stderr: string) => void;

/**
 * Make the mocked `exec` behave as if `ocamlfind` knows exactly the given
 * findlib packages, each mapped to the version string it reports.
 * Returns the list of packages that were queried, in order.
 */
function fakeOcamlfind(installed: Record<string, string>): string[] {
  const queried: string[] = [];
  jest
    .mocked(exec)
    .mockImplementation(((command: string, _opts: unknown, cb: ExecCallback) => {
      const pkg = command.split(" ").pop()!;
      queried.push(pkg);
      if (pkg in installed) {
        cb(null, `${installed[pkg]}\n`, "");
      } else {
        cb(
          new Error(`ocamlfind: Package \`${pkg}' not found`),
          "",
          "",
        );
      }
    }) as unknown as typeof exec);
  return queried;
}

function makeChecker() {
  return new VersionChecker({} as ExtensionContext, ">=0.2.0", ">=3.0.0");
}

beforeEach(() => {
  jest.clearAllMocks();
});

describe("VersionChecker.checkWaterproofLib", () => {
  it("finds rocq-waterproof", async () => {
    const queried = fakeOcamlfind({ "rocq-waterproof.plugin": "3.1.1+9.1" });

    const result = await makeChecker().checkWaterproofLib();

    expect(result).not.toHaveProperty("reason");
    if ("reason" in result) return;
    expect(result.wpVersion.toString()).toBe("3.1.1");
    expect(result.requiredRocqVersion.toString()).toBe("9.1.*");
    expect(queried).toEqual(["rocq-waterproof.plugin"]);
  });

  it("falls back to coq-waterproof for older installations", async () => {
    const queried = fakeOcamlfind({ "coq-waterproof.plugin": "2.2.0+8.17" });

    const result = await makeChecker().checkWaterproofLib();

    expect(result).not.toHaveProperty("reason");
    if ("reason" in result) return;
    expect(result.wpVersion.toString()).toBe("2.2.0");
    expect(queried).toEqual([
      "rocq-waterproof.plugin",
      "coq-waterproof.plugin",
    ]);
  });

  it("prefers rocq-waterproof when both are installed", async () => {
    const queried = fakeOcamlfind({
      "rocq-waterproof.plugin": "3.1.1+9.0",
      "coq-waterproof.plugin": "3.0.0+9.0",
    });

    const result = await makeChecker().checkWaterproofLib();

    expect(result).not.toHaveProperty("reason");
    if ("reason" in result) return;
    expect(result.wpVersion.toString()).toBe("3.1.1");
    expect(queried).toEqual(["rocq-waterproof.plugin"]);
  });

  it("reports both failures when neither is installed", async () => {
    fakeOcamlfind({});

    const result = await makeChecker().checkWaterproofLib();

    expect(result).toHaveProperty("reason");
    if (!("reason" in result)) return;
    expect(result.reason).toContain("rocq-waterproof.plugin");
    expect(result.reason).toContain("coq-waterproof.plugin");
    expect(result.reason).toContain("not found");
  });

  it("runs ocamlfind from the same directory as the configured binary", async () => {
    fakeOcamlfind({ "rocq-waterproof.plugin": "3.1.1+9.1" });

    await makeChecker().checkWaterproofLib();

    const ext = process.platform === "win32" ? ".exe" : "";
    expect(jest.mocked(exec).mock.calls[0][0]).toBe(
      `/opt/wp/bin/ocamlfind${ext} query -format %v rocq-waterproof.plugin`,
    );
  });
});
