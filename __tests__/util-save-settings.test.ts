// NOTE: These tests were AI-generated. They describe the current behaviour of the code and
// may therefore codify existing buggy behaviour; a failing test is not necessarily a regression.

import { beforeEach, describe, expect, it, jest } from "@jest/globals";

// Settings in the `files` section, as returned by the mocked `workspace.getConfiguration`.
let settings: Record<string, boolean> = {};

jest.mock(
  "vscode",
  () => ({
    extensions: { getExtension: jest.fn(), all: [] },
    window: {
      showWarningMessage: jest.fn(() => Promise.resolve(undefined)),
    },
    workspace: {
      getConfiguration: jest.fn(() => ({
        get: (key: string, def?: unknown) => settings[key] ?? def,
      })),
    },
    commands: { executeCommand: jest.fn() },
    env: {},
  }),
  { virtual: true },
);

jest.mock("../src/helpers", () => ({
  WaterproofConfigHelper: { get: jest.fn(() => false) },
  WaterproofLogger: { log: jest.fn(), debug: jest.fn() },
  WaterproofSetting: {},
  qualifiedSettingName: jest.fn((s: string) => s),
}));

type VSCodeMock = {
  window: { showWarningMessage: jest.Mock };
  workspace: { getConfiguration: jest.Mock };
  commands: { executeCommand: jest.Mock };
};

// `checkTextChangingSaveSettings` remembers what it last warned about in module state, so every
// test loads fresh copies of the module and of the vscode mock.
let util: typeof import("../src/util");
let vscode: VSCodeMock;

beforeEach(() => {
  settings = {};
  jest.resetModules();
  vscode = jest.requireMock("vscode");
  util = jest.requireActual("../src/util");
});

const scope = { languageId: "rocq" };

describe("enabledTextChangingSaveSettings", () => {
  it("returns no settings when none are enabled", () => {
    expect(util.enabledTextChangingSaveSettings(scope)).toEqual([]);
  });

  it("returns every enabled text-changing setting", () => {
    settings = {
      trimTrailingWhitespace: true,
      trimFinalNewlines: false,
      insertFinalNewline: true,
    };
    expect(util.enabledTextChangingSaveSettings(scope)).toEqual([
      "trimTrailingWhitespace",
      "insertFinalNewline",
    ]);
  });

  it("ignores unrelated settings in the files section", () => {
    settings = { autoSave: true, hotExit: true } as never;
    expect(util.enabledTextChangingSaveSettings(scope)).toEqual([]);
  });

  it("reads the settings for the given scope", () => {
    util.enabledTextChangingSaveSettings(scope);
    expect(vscode.workspace.getConfiguration).toHaveBeenCalledWith(
      "files",
      scope,
    );
  });
});

describe("checkTextChangingSaveSettings", () => {
  it("does not warn when no text-changing settings are enabled", () => {
    util.checkTextChangingSaveSettings(scope);
    expect(vscode.window.showWarningMessage).not.toHaveBeenCalled();
  });

  it("names all enabled settings in the warning", () => {
    settings = { trimTrailingWhitespace: true, trimFinalNewlines: true };
    util.checkTextChangingSaveSettings(scope);

    expect(vscode.window.showWarningMessage).toHaveBeenCalledTimes(1);
    const message = vscode.window.showWarningMessage.mock.calls[0][0] as string;
    expect(message).toContain("`files.trimTrailingWhitespace`");
    expect(message).toContain("`files.trimFinalNewlines`");
    expect(message).not.toContain("insertFinalNewline");
  });

  it("does not repeat the warning for the same combination of settings", () => {
    settings = { insertFinalNewline: true };
    util.checkTextChangingSaveSettings(scope);
    util.checkTextChangingSaveSettings(scope);
    expect(vscode.window.showWarningMessage).toHaveBeenCalledTimes(1);
  });

  it("warns again when another setting gets enabled", () => {
    settings = { insertFinalNewline: true };
    util.checkTextChangingSaveSettings(scope);
    settings = { insertFinalNewline: true, trimFinalNewlines: true };
    util.checkTextChangingSaveSettings(scope);
    expect(vscode.window.showWarningMessage).toHaveBeenCalledTimes(2);
  });

  it("warns again when a setting is re-enabled after being turned off", () => {
    settings = { trimTrailingWhitespace: true };
    util.checkTextChangingSaveSettings(scope);
    settings = {};
    util.checkTextChangingSaveSettings(scope);
    settings = { trimTrailingWhitespace: true };
    util.checkTextChangingSaveSettings(scope);
    expect(vscode.window.showWarningMessage).toHaveBeenCalledTimes(2);
  });

  it("opens the settings editor filtered on the enabled settings", async () => {
    settings = { trimTrailingWhitespace: true, insertFinalNewline: true };
    vscode.window.showWarningMessage.mockReturnValueOnce(
      Promise.resolve("Open Settings") as never,
    );
    util.checkTextChangingSaveSettings(scope);
    await Promise.resolve();
    await Promise.resolve();

    expect(vscode.commands.executeCommand).toHaveBeenCalledWith(
      "workbench.action.openSettings",
      "@id:files.trimTrailingWhitespace,files.insertFinalNewline",
    );
  });

  it("does not open the settings editor when the warning is dismissed", async () => {
    settings = { trimTrailingWhitespace: true };
    vscode.window.showWarningMessage.mockReturnValueOnce(
      Promise.resolve("Dismiss") as never,
    );
    util.checkTextChangingSaveSettings(scope);
    await Promise.resolve();
    await Promise.resolve();

    expect(vscode.commands.executeCommand).not.toHaveBeenCalled();
  });
});
