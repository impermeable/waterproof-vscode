# Coqnitive

Version with some extra fixes for the client.

## Installing dependencies
Run `npm install` or `npm i` in the [root](./) folder of the repository.

## Running the extension
Press `F5` in vscode to run the extension.

## Running the tests
Run `npm run test`.

## Error `Property 'replaceAll' does not exist on type 'string'`.
VSCode thinks we are targeting an older version of Node than is specified in our build script.<br>
Insert the following setting into your `.vscode/settings.json` to stop it from displaying:
```json
{
    "js/ts.implicitProjectConfig.target": "ESNext"
}
```