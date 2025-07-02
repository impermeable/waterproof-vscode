# Documentation
## General

All types of messages that are sent between editor and extension (and sometimes from extension to extension) are defined in [`shared`](./shared/).

We make use of the type former:
```ts
type MessageBase<T extends MessageType, B = undefined> =
    B extends undefined ? { type: T, requestId?: number } : { type: T, body: B, requestId?: number };
```
Notes on the type former:
- `T extends MessageType` makes sure `T` is a member of the `MessageType` enum.
- `B = undefined`, defaults `B` to `undefined` (so we don't have to provide for messages that don't include a body)
- `B extends undefined ? A : B`, is the usual ternary operator `if`. When `B extends undefined` (ie. `B = undefined`)
   then we choose `A`, otherwise (`B` is an object) we choose `B`.

### Examples:
`MessageBase<MessageType.ready>` does not contain a body and expands to the type `{ type : MessageType.ready }`

`MessageBase<MessageType.command, { command: string, time?: number}>` does contain a body and expands to
```ts
{
    command: string,
    time?: number
}
```
## Messages
### `applyStepError`
#### Description
The editor sends this message when it encounters an error when trying to apply a step from the ProseMirror transaction steps. Used in `dispatchTransaction` in [editor](../editor/src/kroqed-editor/editor.ts).

#### Body
```ts
string // The error message that was reported
```

### `command`
#### Description
Send by a panel or editor when a 'command' should be executed in the language server. For instance, when the user executes the `Help` command in Waterproof. This message is sent from the panel in charge to the extension with `command: "Help."`.

#### Body
```ts
{
    command: string, // The command to execute (eg. 'Help.' or 'Search "term".')
    time?: number    // Time that the command was sent
}
```

### `cursorChange`
#### Description
The editor sends a `cursorChange` message to the extension when the position of the cursor is updated (The ProseMirror selection is updated).

#### Body
```ts
number // Position of the cursor (offset based) after mapping
```

### `diagnostics`
#### Description
Message that contains the diagnostics in the current document which the extension received from the LSP server. Send to the editor upon receiving from the LSP server.

#### Body
```ts
DiagnosticMessage // Type containing the diagnostics as well as the version of the document the diagnostics correspond to
```

### `docChange`
#### Description
This message is send by the editor for every change that the extension should apply to the document on disk. The 'steps' are mapped trhough the mapping via the `stepUpdate` member function of the mapping.

#### Body
```ts
DocChange | WrappingDocChange // Either the document change that happened (regular insertions or deletions) or a wrapping document change (two insertions that happen *around* some other text, eg when creating an input area)
```

### `editorHistoryChange`
#### Description
Send from the extension to the editor to inform the editor that it should perform either an undo or a redo operation.

#### Body
```ts
HistoryChangeType // Enum type for history changes (Undo / Redo)
```

### `editorReady`
#### Description
Message sent by the editor to inform the Extension Host that it is ready to be used. That is, at this point we can safely query the content using `getFileData` or get the cursor position.

#### Body
This message does not have a body.

### `errorGoals`
#### Description

#### Body
```ts
errorGoals
```

### `init`

#### Description
Send by the extension to start initialization of the webview editor, includes the initial document in the body. The file format is specified in the shared folder as well, currently `.mv` and `.v` are supported.

#### Body
```ts
{
    value: string,        // Contents of the document
    format: FileFormat,   // File format of the document (see FileFormat)
    version: number       // Current version of the document
}
```

### `refreshDocument`

#### Description
Send by the extension to refresh the webview editor, includes the updated content of the document in the body, as well as the documnet's version.

#### Body
```ts
{
    value: string,        // Updated content of the document
    version: number       // Current version of the document
}
```

### `insert`
#### Description
Send by the extension to inform the editor that a symbol should be inserted.

#### Body
```ts
{
    symbolUnicode: string,      // The unicode character that should be inserted
    symbolLatex: string,        // The LaTeX command responsible for producing this character
    type: "symbol" | "tactics", // The type of the insertion ("symbol" for symbols (like alpha), "tactics" for tactics)
    time: number                // Time that the command was executed
}
```

### `lineNumbers`
#### Description
Send in both directions:

- `editor -> extension` to request updates to the set of line numbers.
- `extension -> editor` to update the set of line numbers.


#### Body
```ts
LineNumber // Contains line numbers (as array) and the version of the document they correspond to.
```

### `progress`
#### Description
Send by the extension and used in the editor to determine up to what point the current file has been verified.

#### Body
```ts
SimpleProgressParams // Contains number of lines and a list of program info.
```

### `qedStatus`
#### Description
Send by the extension to the editor. This message includes the status for all the input areas. This includes whether they are checked and whether they are correct.

#### Body
```ts
QedStatus[] // Status per input area, see QedStatus.ts
```

### `ready`
#### Description
The editor sends this message to the extension when it is initialized and ready to react to other messages.

#### Body
This message does not have a body.

### `renderGoals`
#### Description
Message send by the extension when the set of goals changes. Panels (goal, logbook, info) listen to this message to update the set of goals that they show.

#### Body
```ts
unknown // TODO: Currently there is no real guarantee on what kind of data is included.
```

### `response`
#### Description
This message is the response of another message and will call the callback associated with this request (passes the body as arguments to the callback function). See [`webviewManager.ts`](../src/webviewManager.ts) for the implementation.

#### Body
```ts
{
    data: unknown,      // The data belonging to the callback
    requestId: number   // (Unique) id that this response belongs to
}
```

### `setAutocomplete`
#### Description
Send by the extension to the editor when the set of autocompletions changes, for example when a new definition was added to the document.

#### Body
```ts
Completion[] // The array of completions every CodeMirror cell receives.
```

### `setData`
#### Description
Message send by panel controllers to panels to update the data shown within the panel. For example, the goals controller updates the goals shown in the panel.

#### Body
```ts
string[] | GoalAnswer<PpString> // TODO
```

### `setShowLineNumbers`
#### Description
Sent from the extension to the editor to enable/disable line numbers from showing in the editor.

#### Body
```ts
boolean // Flag indicating whether line numbers should be turned on or off
```

### `syntax`
#### Description
Message send by the extension when the syntax mode should be updated. Currently, the two available modes are Waterproof syntax (`false`) or plain Coq syntax (`true`).

#### Body
```ts
boolean // If true, standard Coq syntax completions are given. If false, Waterproof tactic completions are given instead.
```

### `teacher`
#### Description
Sent from the extension to the editor to enable/disable teacher mode in the editor.

#### Body
```ts
boolean // Flag indicating whether teacher mode should be turned on or off
```
