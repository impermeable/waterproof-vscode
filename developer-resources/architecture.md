# Waterproof Architecture

## Overview

Waterproof is a VS Code extension that helps students learn to write mathematical proofs. It provides a rich ProseMirror-based editor for exercise sheets and communicates with a Language Server Protocol (LSP) backend for proof checking, diagnostics, and completions.

The system is composed of four main components:

1. **`waterproof-editor`** — A ProseMirror-based rich-text editor (npm package `@impermeable/waterproof-editor`) that runs inside a VS Code webview. It handles document editing, rendering, and user interaction (cursor changes, input areas, symbols, tactics). Supports multiple file formats: `.mv` (MarkdownV), `.v` (RegularV), and `.lean` (Lean), each with its own document serializer.

2. **`waterproof-vscode`** — The VS Code extension host logic. It orchestrates everything: manages webviews via the `WebviewManager`, routes messages between the editor and the LSP clients, handles file I/O through VS Code's `CustomTextEditorProvider`, and provides side panels (goals, search, help, tactics, symbols, execute, debug). A `CompositeClient` manages both Rocq and Lean LSP clients simultaneously, routing requests to the correct client based on `document.languageId`.

3. **VS Code** — The host application providing the extension API, webview infrastructure, text document model, command palette, and UI chrome (status bar, side panels, themes).

4. **LSP (Language Servers)** — Two external language server processes run concurrently (note that students will generally use just one in practice):
   - **rocq-lsp** for Rocq (`.mv` and `.v` files) — provides proof checking, diagnostics, goal information, completions, and command execution.
   - **Lean Language Server** via `lake serve` for Lean (`.lean` files) — provides proof checking, diagnostics, and goal information.

## Component Diagram

The diagram below shows how these four components relate to each other.

```mermaid
graph LR
    subgraph "VS Code (Host Application)"
        direction TB
        VSCODE_API["VS Code Extension API<br/><small>TextDocument, WebviewPanel,<br/>commands, workspace</small>"]
    end

    subgraph "waterproof-vscode (Extension Host)"
        direction TB
        EXT["Waterproof<br/><small>extension.ts</small>"]
        WVM["WebviewManager<br/><small>webviewManager.ts</small>"]
        PROV["CoqEditorProvider<br/><small>CustomTextEditorProvider</small>"]
        COMP["CompositeClient<br/><small>composite.ts</small>"]
        ROCQ_C["RocqLspClient<br/><small>lsp-client/rocq/client.ts</small>"]
        LEAN_C["LeanLspClient<br/><small>lsp-client/lean/client.ts</small>"]
        PANELS["Side Panels<br/><small>Goals, Tactics, Symbols,<br/>Search, Help, Execute</small>"]

        subgraph "waterproof-editor (Webview)"
            direction TB
            PM["WaterproofEditor<br/><small>ProseMirror-based<br/>rich-text editor</small>"]
            MAP["Document Mapping<br/><small>TextDocMappingMV / V / Lean</small>"]
            PM --- MAP
        end

        EXT --- WVM
        EXT --- COMP
        COMP --- ROCQ_C
        COMP --- LEAN_C
        EXT --- PROV
        WVM --- PANELS
        WVM --- PROV
    end

    subgraph "LSP"
        direction TB
        COQ_LSP["coq-lsp<br/><small>Rocq Language Server</small>"]
        LEAN_LSP["lake serve<br/><small>Lean Language Server</small>"]
    end

    PM -- "Messages<br/>(postMessage)" --> WVM
    WVM -- "Messages<br/>(postMessage)" --> PM

    PROV -- "TextDocument<br/>read/write" --> VSCODE_API
    EXT -- "Extension API<br/>commands, config" --> VSCODE_API

    ROCQ_C -- "LSP Protocol<br/>(JSON-RPC)" --> COQ_LSP
    COQ_LSP -- "Diagnostics, Goals,<br/>Completions" --> ROCQ_C
    LEAN_C -- "LSP Protocol<br/>(JSON-RPC)" --> LEAN_LSP
    LEAN_LSP -- "Diagnostics, Goals" --> LEAN_C
```

### Interaction Flow

1. **Document open**: VS Code opens an `.mv`, `.v`, or `.lean` file and activates the `CoqEditorProvider`, which creates a `ProseMirrorWebview`. The webview loads the `waterproof-editor` bundle with the appropriate document serializer and mapping for the file format, and initializes a ProseMirror editor instance with the document content.

2. **Editing**: When the user edits the document in the ProseMirror editor, changes are sent as `docChange` messages to the extension host via `postMessage`. The `ProseMirrorWebview` applies these changes to the VS Code `TextDocument` through a `SequentialEditor`. VS Code's document model then notifies the appropriate LSP client of the change.

3. **Language routing**: The `CompositeClient` inspects `document.languageId` to route requests to the correct LSP client. Documents with `languageId === 'lean4'` (`.lean` files) are handled by `LeanLspClient`; all others (`.mv`, `.v`) are handled by `RocqLspClient`.

4. **Proof checking**: The LSP server reads the exercise sheets on disk, and communicates the diagnostics through the LSP client. These diagnostics are routed through the `WebviewManager` to the editor as `diagnostics` messages.

5. **Goal display**: When the cursor moves, the editor sends a `cursorChange` message. The `CompositeClient` delegates to the active client, which queries its language server for goals at that position. For Rocq, goals are returned as structured `PpString` objects; for Lean, goals are returned as plain strings via the `$/lean/plainGoal` request. Results are rendered in the Goals side panel.

6. **Input area status**: Both clients determine proof status within input areas. In `.mv` files, input areas are delimited by `<input-area>` tags. In Lean files, input areas use `:::input` / `:::` delimiters. The `LeanLspClient` checks proof status by requesting goals at the end of each input area; an empty goals list indicates a correct proof.

7. **Commands**: Help commands originate from side panels, flow through the `WebviewManager`, and are executed via the LSP client. Note: the Lean client does not currently support viewport hints or arbitrary command execution.

## Deployment Diagram

The deployment diagram shows the runtime environment for Waterproof, including the proof assistants it supports (Rocq and Lean) and their dependency management.

```mermaid
graph TB
    subgraph "VS Code"
        direction LR
        WP_EXT["Waterproof Extension<br/><small>waterproof-vscode</small>"]
        EDITOR_WV["Editor Webview<br/><small>waterproof-editor</small>"]
        SIDE_PANELS["Side Panels<br/><small>Goals, Tactics, Symbols,<br/>Search, Help</small>"]

        WP_EXT --- EDITOR_WV
        WP_EXT --- SIDE_PANELS
    end

    subgraph "Rocq Installation (opam / installer)"
        direction TB
        ROCQ_LSP["rocq-lsp<br/><small>Language Server</small>"]
        COQ_WP["coq-waterproof<br/><small>Proof automation library<br/>included in local Rocq install</small>"]
        COQ_STDLIB["Rocq Standard Library"]

        ROCQ_LSP --- COQ_WP
        ROCQ_LSP --- COQ_STDLIB
    end

    subgraph "Lean Installation (elan)"
        direction TB
        LEAN_LSP["lake serve<br/><small>Lean Language Server</small>"]
    end

    subgraph "Local Folder (Rocq Project)"
        direction TB
        MV_FILES[".mv / .v files<br/><small>Proof documents</small>"]
    end

    subgraph "Local Folder (Lean Project)"
        direction TB
        LEAN_FILES[".lean files<br/><small>Proof documents</small>"]
        LAKE_CFG["lakefile.lean / lakefile.toml<br/><small>declares dependencies</small>"]
        LAKE_MANIFEST["lake-manifest.json<br/><small>version pinning</small>"]
        LAKE_PKGS[".lake/packages/<br/><small>dependencies pulled by Lake</small>"]
        WP_GENRE["Waterproof Genre<br/><small>Verso-based file support<br/>and GoalWidget</small>"]
        VERBOSE_LEAN["Verbose Lean<br/><small>Proof language support</small>"]

        LEAN_TOOLCHAIN["lean-toolchain<br/><small>pins Lean version</small>"]

        LAKE_CFG --- LAKE_PKGS
        LAKE_CFG --- LAKE_MANIFEST
        LAKE_PKGS --- WP_GENRE
        LAKE_PKGS --- VERBOSE_LEAN
    end

    WP_EXT -- "LSP (JSON-RPC / stdio)" --> COQ_LSP
    WP_EXT -- "LSP (JSON-RPC / stdio)" --> LEAN_LSP
    ROCQ_LSP -- "reads" --> MV_FILES
    LEAN_LSP -- "reads" --> LEAN_FILES
    LEAN_LSP -- "reads" --> LAKE_CFG
    LEAN_LSP -- "reads" --> LEAN_TOOLCHAIN
    WP_EXT -- "File I/O" --> MV_FILES
    WP_EXT -- "File I/O" --> LEAN_FILES

    %% Force vertical layout: VS Code above installations, installations above local folders
    EDITOR_WV ~~~ COQ_LSP
    SIDE_PANELS ~~~ LEAN_LSP
    COQ_WP ~~~ MV_FILES
    LEAN_TOOLCHAIN ~~~ LEAN_FILES
```

### Rocq Deployment

For Rocq-based projects, the language server is **rocq-lsp**. The extension communicates with it over JSON-RPC. The required libraries are part of the local Rocq/opam installation:

- **coq-lsp** is installed via opam
- **coq-waterproof** is a Rocq plugin that provides proof automation tactics tailored for Waterproof. It is installed into the same opam switch, making it available to coq-lsp at runtime.
- On Windows, a bundled installer can set up all Rocq dependencies in a self-contained folder.


### Lean Deployment

To run Lean projects, Lean must be installed through `elan`. This provides access
to the `lake` command, which is used to manage dependencies.

For Lean-based projects, the language server is started via **`lake serve`**. The extension runs `lake serve` as the LSP server process, configured through the `waterproof.lakePath` setting (defaults to `lake` on PATH) and optional `waterproof.lakeArgs` arguments.

Before starting the Lean client, a prelaunch check verifies that `lake --version` executes successfully. If this fails (e.g. Lake is not installed), the Lean client is skipped and only the Rocq client starts.

The Lean project folder must contain:

- **`lakefile.lean`** or **`lakefile.toml`** — declares project dependencies. Lake pulls required packages from remote Git repositories into the `.lake/packages/` directory. A dependency on the Waterproof Genre is necessary. This provides LSP support
on markdown-esque files through Verso, as well as a GoalWidget for better goal display. A dependency on Verbose Lean, which provides proof language support,
is required (unless the exercise sheet is plain Lean).
- **`lean-toolchain`** — pins the Lean version for the project.
- **`lake-manifest.json`** — locks dependency versions for reproducible builds.

Dependencies are cached locally after the first fetch. The Lean language server resolves imports using the Lake build configuration and provides proof checking, diagnostics, and goal information.

**Key differences from the Rocq client:**
- Goals are requested via `$/lean/plainGoal` (returns plain strings) instead of the Rocq `proof/goals` endpoint (returns structured `PpString` objects).
- Viewport hints (`sendViewportHint`) are not supported.
- Input areas in `.lean` files are delimited by `:::input` / `:::` markers rather than XML-style `<input-area>` tags.
- File progress notifications use Lean's `$/lean/fileProgress` notification type.
- The `LeanLspClient` exposes additional event emitters (`didChange`, `didClose`, `diagnostics`, `customNotification`, `clientStopped`) for potential infoview integration via the `@leanprover/infoview-api` package.
