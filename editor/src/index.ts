import { FileFormat, Message, MessageType } from "../../shared";
import {
  defaultToMarkdown,
  markdown,
  ThemeStyle,
  WaterproofEditor,
  WaterproofEditorConfig,
  wrapInContainer,
} from "@impermeable/waterproof-editor";
// TODO: The tactics completions are static, we want them to be dynamic (LSP supplied and/or configurable when the editor is running)
import waterproofTactics from "../../completions/tactics.json";
import leanTactics from "../../completions/tacticsLean.json";
import rocqTactics from "../../completions/tacticsRocq.json";
import symbols from "../../completions/symbols+lean.json";

// import style sheet and fonts from waterproof-editor
import "@impermeable/waterproof-editor/styles.css";
// import the style sheet mapping waterproof style properties to vscode styles
import "./vscodemapping.css";
import { vFileParser } from "./document-construction/vFile";
import { rocqdocToMarkdown } from "./rocqdoc";
import { topLevelBlocksLean } from "./document-construction/construct-document";
import { tagConfigurationV } from "./vFileConfiguration";
import * as langWp from "@impermeable/codemirror-lang-waterproof";
import * as langVerbose from "@impermeable/codemirror-lang-verbose";
import * as langRocq from "@impermeable/codemirror-lang-rocq";
import { tagConfigurationLean } from "./leanFileConfiguration";
import { LeanSerializer } from "./leanSerializer";
import { versoMarkdownToMarkdown } from "./versoMarkdownSupport";
import { handleEditorMessage } from "./messageHandler";

/**
 * Very basic representation of the acquirable VSCodeApi.
 * At least supports `postMessage(message: Message)`.
 */
interface VSCodeAPI {
  postMessage: (message: Message) => void;
}

function createConfiguration(
  format: FileFormat,
  codeAPI: VSCodeAPI,
  editorRef: { current?: WaterproofEditor },
) {
  let formatConf: Pick<
    WaterproofEditorConfig,
    | "completions"
    | "documentConstructor"
    | "toMarkdown"
    | "markdownName"
    | "tagConfiguration"
    | "languageConfig"
    | "disableMarkdownFeatures"
    | "serializer"
    | "menubarEntries"
  >;

  // Set format-specific configuration
  switch (format) {
    case FileFormat.MarkdownV:
      formatConf = {
        completions: waterproofTactics,
        documentConstructor: (v: string) =>
          markdown.parse(v, { language: "coq" }),
        toMarkdown: defaultToMarkdown,
        markdownName: "Markdown",
        tagConfiguration: markdown.configuration("coq"),
        languageConfig: {
          highlightDark: langWp.highlight_dark,
          highlightLight: langWp.highlight_light,
          languageSupport: langWp.waterproof(),
        },
      };
      break;
    case FileFormat.RegularV:
      formatConf = {
        completions: rocqTactics,
        documentConstructor: vFileParser,
        toMarkdown: rocqdocToMarkdown,
        markdownName: "Rocq doc",
        tagConfiguration: tagConfigurationV,
        disableMarkdownFeatures: ["code"],
        languageConfig: {
          languageSupport: langRocq.rocq(),
          highlightDark: langRocq.highlight_dark,
          highlightLight: langRocq.highlight_light,
        },
      };
      break;
    case FileFormat.Lean:
      formatConf = {
        completions: leanTactics,
        documentConstructor: topLevelBlocksLean,
        toMarkdown: versoMarkdownToMarkdown,
        markdownName: "Markdown",
        tagConfiguration: tagConfigurationLean,
        serializer: new LeanSerializer(),
        languageConfig: {
          highlightDark: langVerbose.highlight_dark,
          highlightLight: langVerbose.highlight_light,
          languageSupport: langVerbose.verbose(),
        },
        menubarEntries: [
          {
            title: "M...",
            hoverText: "Wrap selection in a container (groups math evaluation)",
            callback: () => {
              editorRef.current?.executeProsemirrorCommand(
                wrapInContainer(tagConfigurationLean, "multilean"),
              );
            },
            isActive: (state) =>
              wrapInContainer(tagConfigurationLean, "multilean")(
                state,
                undefined,
              ),
            buttonVisibility: { teacherModeOnly: true },
          },
        ],
      };
      break;
  }

  // Create the WaterproofEditorConfig object
  const cfg: WaterproofEditorConfig = {
    // Include format-specific configuration
    ...formatConf,

    symbols: symbols,
    api: {
      executeHelp() {
        codeAPI.postMessage({
          type: MessageType.command,
          body: { command: "Help.", time: new Date().getTime() },
        });
      },
      executeCommand(command: string, time: number) {
        codeAPI.postMessage({
          type: MessageType.command,
          body: { command, time },
        });
      },
      editorReady() {
        codeAPI.postMessage({ type: MessageType.editorReady });
      },
      documentChange(change) {
        codeAPI.postMessage({ type: MessageType.docChange, body: change });
      },
      applyStepError(errorMessage) {
        codeAPI.postMessage({
          type: MessageType.applyStepError,
          body: errorMessage,
        });
      },
      cursorChange(cursorPosition) {
        codeAPI.postMessage({
          type: MessageType.cursorChange,
          body: cursorPosition,
        });
      },
      viewportHint(start, end) {
        codeAPI.postMessage({
          type: MessageType.viewportHint,
          body: { start, end },
        });
      },
    },
  };

  return cfg;
}

window.onload = () => {
  // Get HTML DOM elements
  const editorElement = document.querySelector<HTMLElement>("#editor");

  if (editorElement == null) {
    throw Error(
      "Editor element cannot be null (no element with id 'editor' found)",
    );
  }

  const codeAPI = acquireVsCodeApi() as VSCodeAPI;
  if (codeAPI == null) {
    throw Error("Could not acquire the vscode api.");
    // TODO: maybe sent some sort of test message?
  }
  const format = document.body.getAttribute("format") as FileFormat;

  // Create a ref so that menubar callbacks can dispatch commands after the editor is constructed.
  const editorRef: { current?: WaterproofEditor } = {};

  // Create the editor, passing it the vscode api and the editor and content HTML elements.
  const cfg = createConfiguration(format, codeAPI, editorRef);
  // Retrieve the current theme style from the attribute 'data-theme-kind'
  // attached to the editor element. This allows us to set the initial theme kind
  // rather than waiting for the themestyle message to arrive.
  const themeStyle: ThemeStyle = (() => {
    const value = editorElement.getAttribute("data-theme-kind");
    if (value === null) {
      throw Error("Could not get theme style from editor element");
    }

    switch (value) {
      case "dark":
        return ThemeStyle.Dark;
      case "light":
        return ThemeStyle.Light;
      default:
        throw Error("Invalid theme encountered");
    }
  })();
  const editor = new WaterproofEditor(editorElement, cfg, themeStyle);
  editorRef.current = editor;

  //@ts-expect-error For now, expose editor in the window. Allows for calling editorInstance methods via the debug console.
  window.editorInstance = editor;

  // Register event listener for communication between extension and editor
  window.addEventListener("message", (event: MessageEvent<Message>) => {
    const msg = event.data;

    handleEditorMessage(editor, msg);
  });

  let timeoutHandle: number | undefined;
  window.addEventListener("scroll", (_event) => {
    if (timeoutHandle === undefined) {
      timeoutHandle = window.setTimeout(() => {
        editor.handleScroll(window.innerHeight);
        timeoutHandle = undefined;
      }, 100);
    }
  });

  // Start the editor
  codeAPI.postMessage({ type: MessageType.ready });
};
