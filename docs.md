# Documentation
## Messages
The general message structure is as [follows](./shared/):
```js 
{
    type: MessageType, 
    body?: any, 
    requestId?: number
}
```
#### `MessageType.init`
The message sent by VSCode to start initialization of the webview editor, includes the initial document in `body.value`. Structure of the message: 
```js
{
    type: MessageType.init,
    body: {
        value: <Uint8Array>,
    }
} 
```
#### `MessageType.getFileData`
The message sent by VSCode to query the current document content. Structure: 
```js
{
    type: MessageType.getFileData,
    requestId: <number>
} 
```

#### `MessageType.response`
Response message sent from the editor, will resolve a promise on the Extension side. 
```js
{
    type: MessageType.response, 
    requestId: <number>,
    body: any
}
```

#### `MessageType.redo`
Message sent by VSCode when the editor should execute an undo event. 
```js
{
    type: MessageType.redo
}
```

#### `MessageType.undo`
Message sent by VSCode when the editor should execute a redo event.
```js
{ 
    type: MessageType.undo
}
```

#### `MessageType.update`
Message sent by the Extension Host to inform the internal editor that the content has been updated.
```js
{
    type: MessageType.update
}
```

#### `MessageType.ready`
Message sent by the editor to inform the Extension Host that it is ready to recieve messages. 
```js
{
    type: MessageType.ready
}
```

#### `MessageType.editorReady`
Message sent by the editor to inform the Extension Host that it is ready to be used. Ie. at this point we can safely query the content using `getFileData` or get the cursor position.
```js
{
    type: MessageType.editorReady
}
```

#### `MessageType.docChange`
Message sent by the editor to inform the Extension Host that an edit has been made in the prosemirror instance.
```js
{
    type: MessageType.docChange
}
```

#### `MessageType.insertSymbol`
Message sent by the Extension Host to inform the editor that a symbol should be inserted. 
```js
{
    type: MessageType.insertSymbol, 
    body: {
        symbolUnicode: <unicode character(s) of the symbol>, 
        symbolLaTeX: <latex command to produce the character(s)>
    }
}
```