// LLM-generated tests that might codify existing (wrong) behaviour.

import { Position } from "vscode";
import {
  executeCommand,
  executeCommandFullOutput,
} from "../../src/lsp-client/commandExecutor";
import {
  getStateAtPosReq,
  goalsReq,
  runReq,
} from "../../src/lsp-client/petanque";
import type { RocqLspClient } from "../../src/lsp-client/rocq/client";
import { makeClientDouble } from "../__helpers__/lsp-client-mocks";
import type { mocks as MockFactories } from "../__helpers__/lsp-client-mocks";

function lspMocks(): typeof MockFactories {
  return require("../__helpers__/lsp-client-mocks").mocks; // eslint-disable-line @typescript-eslint/no-require-imports
}

// commandExecutor only touches `vscode` (Position), `vscode-languageclient`
// (RequestType, loaded transitively via ./petanque) and
// `vscode-languageserver-types` (VersionedTextDocumentIdentifier).
jest.mock("vscode", () => lspMocks().vscode(), { virtual: true });
jest.mock("vscode-languageclient", () => lspMocks().languageClient(), {
  virtual: true,
});
jest.mock(
  "vscode-languageserver-types",
  () => lspMocks().languageServerTypes(),
  { virtual: true },
);

const URI = "file:///proof.v";
const VERSION = 7;

type ClientOverrides = {
  activeDocument?: unknown;
  sentenceStart?: Position | undefined;
};

/**
 * Build a minimal `RocqLspClient` double. Only the three members the
 * command executor uses are populated: `activeDocument`,
 * `getBeginningOfCurrentSentence` and the underlying language `client`.
 */
function makeFakeClient(overrides: ClientOverrides = {}) {
  const languageClient = makeClientDouble();

  const document = {
    uri: { toString: () => URI },
    version: VERSION,
  };

  const client = {
    activeDocument:
      "activeDocument" in overrides ? overrides.activeDocument : document,
    getBeginningOfCurrentSentence: jest.fn(() =>
      "sentenceStart" in overrides
        ? overrides.sentenceStart
        : new Position(4, 5),
    ),
    client: languageClient,
  } as unknown as RocqLspClient;

  return { client, languageClient };
}

const STATE_RES = { st: 10, proof_finished: false, feedback: [] };
const RUN_RES = {
  st: 20,
  proof_finished: true,
  feedback: [
    [1, "hello"],
    [2, "world"],
  ] as [number, string][],
};
const GOALS_RES = {
  goals: [{ ty: "True", hyps: [] }],
  stack: [],
  bullet: null,
};

/**
 * Route `sendRequest` responses by request type so that the three sequential
 * calls (get_state_at_pos -> run -> goals) each return their own payload.
 */
function stubRequests(
  languageClient: ReturnType<typeof makeClientDouble>,
  responses: {
    state?: unknown;
    run?: unknown;
    goals?: unknown;
  } = {},
) {
  (languageClient.sendRequest as jest.Mock).mockImplementation(
    (req: unknown) => {
      if (req === getStateAtPosReq)
        return Promise.resolve(responses.state ?? STATE_RES);
      if (req === runReq) return Promise.resolve(responses.run ?? RUN_RES);
      if (req === goalsReq)
        return Promise.resolve(responses.goals ?? GOALS_RES);
      return Promise.reject(new Error("unexpected request"));
    },
  );
}

describe("commandExecutor", () => {
  describe("executeCommand", () => {
    it("returns a GoalAnswer<string> with mapped feedback, goals and document", async () => {
      const { client, languageClient } = makeFakeClient();
      stubRequests(languageClient);

      const result = await executeCommand(
        client,
        "reflexivity.",
        new Position(1, 2),
      );

      expect(result.messages).toEqual([
        { level: 1, text: "hello" },
        { level: 2, text: "world" },
      ]);
      expect(result.position).toEqual(new Position(0, 0));
      expect(result.textDocument).toEqual({ uri: URI, version: VERSION });
      expect(result.goals).toBe(GOALS_RES);
    });

    it("produces an empty messages array when there is no feedback", async () => {
      const { client, languageClient } = makeFakeClient();
      stubRequests(languageClient, { run: { ...RUN_RES, feedback: [] } });

      const result = await executeCommand(client, "idtac.", new Position(1, 2));

      expect(result.messages).toEqual([]);
    });
  });

  describe("executeCommandFullOutput", () => {
    it("returns the goals config merged with the run result", async () => {
      const { client, languageClient } = makeFakeClient();
      stubRequests(languageClient);

      const result = await executeCommandFullOutput(
        client,
        "reflexivity.",
        new Position(1, 2),
      );

      expect(result).toEqual({ ...GOALS_RES, ...RUN_RES });
    });
  });

  describe("request threading", () => {
    it("issues get_state_at_pos, run and goals in order with state threaded", async () => {
      const { client, languageClient } = makeFakeClient();
      stubRequests(languageClient);
      const send = languageClient.sendRequest as jest.Mock;

      const pos = new Position(3, 8);
      await executeCommand(client, "auto.", pos);

      expect(send).toHaveBeenCalledTimes(3);

      const [stateReq, stateParams] = send.mock.calls[0];
      expect(stateReq).toBe(getStateAtPosReq);
      expect(stateParams).toEqual({ position: pos, uri: URI });

      const [runRequest, runParams] = send.mock.calls[1];
      expect(runRequest).toBe(runReq);
      expect(runParams).toEqual({ st: STATE_RES.st, tac: "auto." });

      const [goalsRequest, goalsParams] = send.mock.calls[2];
      expect(goalsRequest).toBe(goalsReq);
      expect(goalsParams).toEqual({ st: RUN_RES.st });
    });
  });

  describe("position resolution when pos is omitted", () => {
    it("uses the sentence start and decrements the character by one", async () => {
      const { client, languageClient } = makeFakeClient({
        sentenceStart: new Position(4, 5),
      });
      stubRequests(languageClient);
      const send = languageClient.sendRequest as jest.Mock;

      await executeCommand(client, "auto.");

      expect(client.getBeginningOfCurrentSentence).toHaveBeenCalled();
      const [, stateParams] = send.mock.calls[0];
      expect(stateParams.position).toEqual(new Position(4, 4));
    });

    it("clamps the character to 0 when the sentence starts at character 0", async () => {
      const { client, languageClient } = makeFakeClient({
        sentenceStart: new Position(2, 0),
      });
      stubRequests(languageClient);
      const send = languageClient.sendRequest as jest.Mock;

      await executeCommand(client, "auto.");

      const [, stateParams] = send.mock.calls[0];
      expect(stateParams.position).toEqual(new Position(2, 0));
    });

    it("prefers the explicit pos and does not consult the sentence start", async () => {
      const { client, languageClient } = makeFakeClient();
      stubRequests(languageClient);
      const send = languageClient.sendRequest as jest.Mock;

      const pos = new Position(9, 9);
      await executeCommand(client, "auto.", pos);

      expect(client.getBeginningOfCurrentSentence).not.toHaveBeenCalled();
      const [, stateParams] = send.mock.calls[0];
      expect(stateParams.position).toBe(pos);
    });
  });

  describe("error handling", () => {
    it("throws when there is no active document", async () => {
      const { client } = makeFakeClient({ activeDocument: undefined });

      await expect(
        executeCommand(client, "auto.", new Position(0, 0)),
      ).rejects.toThrow("there is no active document");
    });

    it("throws when pos is omitted and the document has no Coq code", async () => {
      const { client } = makeFakeClient({ sentenceStart: undefined });

      await expect(executeCommand(client, "auto.")).rejects.toThrow(
        "contains no Coq code",
      );
    });

    it("wraps request failures and includes the command name", async () => {
      const { client, languageClient } = makeFakeClient();
      (languageClient.sendRequest as jest.Mock).mockRejectedValue(
        new Error("boom"),
      );

      await expect(
        executeCommand(client, "reflexivity.", new Position(0, 0)),
      ).rejects.toThrow(/reflexivity\..*boom/);
    });

    it("also wraps request failures for executeCommandFullOutput", async () => {
      const { client, languageClient } = makeFakeClient();
      (languageClient.sendRequest as jest.Mock).mockRejectedValue(
        new Error("kapow"),
      );

      await expect(
        executeCommandFullOutput(client, "lia.", new Position(0, 0)),
      ).rejects.toThrow(/lia\..*kapow/);
    });
  });
});
