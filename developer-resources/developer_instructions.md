# Waterproof

## Git lfs

This repository uses git lfs for building the web version of the extension.
Install git lfs from your package manager or from [here](https://git-lfs.com/).
Be sure to run `git lfs pull` to update the files tracked in lfs. (All these files are in the `vendor` folder.)

## Installing dependencies
Run `npm install` or `npm i` in the [root](./) folder of the repository.

### Using a local version of `waterproof-editor`
When working on the [`waterproof-editor`](https://github.com/impermeable/waterproof-editor/) project in conjunction with `waterproof-vscode`, it is often desired to 'link' your local version of `waterproof-editor` to this repository. Changes made in the editor project will then be automatically reflected here. This can be done by following the steps underneath:

1. In the root directory of `waterproof-editor` run `npm link`.
2. Run the watch tasks to continuously build the sources in `waterproof-editor`, that way manual building after making changes is not needed. The watch tasks can be executed with
    ```
    node esbuild.mjs --watch
    ```
    and
    ```
    npx tsc -b --watch
    ```
    Alternatively, when using VSCode/Codium, run the `watch` task by opening the command pallete, using the command `Tasks: Run Task` and selecting `watch`.
3. In the root of this repository run `npm link @impermeable/waterproof-editor`, this will tell npm to use the 'linked version' of `waterproof-editor`. 

**Note**: The link is removed when installing dependencies using `npm i` or `npm ci`. If desired, the link should be set up again following the steps above after running one of these commands. 

## Running the extension
Press `F5` in vscode to run the extension.

## Running unit tests
Run `npm run unit-tests`.

This will execute the unit tests as defined in [`__tests__`](../__tests__/).

## Running Cypress tests
Run `npm run cypress-tests`.

This will execute the `e2e` tests as defined in [`cypress/e2e`](../cypress/e2e/).

Run `npx cypress open` to start the Cypress app.

## Running the typechecker
Run `npm run typecheck`.

## Running the linter
Run `npm run lint`. Some common problems can be automatically fixed with `npm run lint-fix`.

## Error `Property 'replaceAll' does not exist on type 'string'`.
VSCode thinks we are targeting an older version of Node than is specified in our build script.<br>
Insert the following setting into your `.vscode/settings.json` to stop it from displaying:
```json
{
    "js/ts.implicitProjectConfig.target": "ESNext"
}
```

## Publishing the extension: regular release
Make sure to run
```
git pull
```
and
```
git pull lfs
```
Run
```
npm ci
```
Make sure the version numbers are correct.
In particular, because this is a regular version, make sure that the version number is of the form
\*.EVEN.\*, see [here](https://code.visualstudio.com/api/working-with-extensions/publishing-extension) for why.
Run
```
npm run package
```
The extension is packaged as `test_out/extension.vsix`.
This `.vsix` file can now be published on the vscode marketplace.

Finally, tag the commit with the version number, and push the tag to the repository.

## Publishing the extension: a pre-release
Make sure to run
```
git pull
```
and
```
git pull lfs
```
Run
```
npm ci
```
Make sure the version numbers are correct.
In particular, because this is a pre-release version, make sure that the version number is of the form
\*.ODD.\*, see [here](https://code.visualstudio.com/api/working-with-extensions/publishing-extension) for why.
Run
```
npm run package-pre-release
```
The extension is packaged as `test_out/extension.vsix`.
This `.vsix` file can now be published on the vscode marketplace.

Finally, tag the commit with the version number, and push the tag to the repository.

### Running a debug version of the webextension
TODO: Update instructions
1. Obtain `coq-lsp_worker and front-end.zip` from the coq-lsp CI artifacts. (Latest build at the time of writing: https://github.com/ejgallego/coq-lsp/actions/runs/13566988935) (Build for 8.17 has serlib errors at this point in time).
2. Unzip the file. Move `coq_lsp_worker.bc.js` to `out.
3. Run the `Run Web Extension in VS Code` task.
