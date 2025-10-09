# Waterproof

## Git lfs

This repository uses git lfs for building the web version of the extension.
Install git lfs from your package manager or from [here](https://git-lfs.com/).
Be sure to run `git lfs pull` to update the files tracked in lfs. (All these files are in the `vendor` folder.)

## Installing dependencies
Run `npm install` or `npm i` in the [root](./) folder of the repository.

## Linking `waterproof-editor`
An integral part of the experience of `waterproof-vscode` is the custom editor we have developed. The editor, `waterproof-editor`, is developed in a [different repository](https://github.com/impermeable/waterproof-editor/) and usually installed separately via `npm`. During development (or debugging) of features related to the editor it is usefull to 'link' the editor project. This allows npm to resolve the dependency locally and any changes made to the editor will automatically be included in the waterproof-vscode project. 

To link the editor: 
1. Clone the [waterproof-editor repository](https://github.com/impermeable/waterproof-editor) and `cd` into it.
2. Install its dependencies with `npm i`
3. Compile the sources and the types using `node esbuild.mjs` and `npx tsc -b`. <br>*Note*: During development it may be easier to run compilation in 'watch' mode by running `node esbuild.mjs --watch` and `npx tsc -b --watch` in separate terminal windows. This can also be achieved by using the 'task' functionality in VSCode/Codium, by using the command palette, using `Tasks: Run Task` and selecting `watch` or `watch:debug` (see the waterproof-editor documentation for info on `watch:debug`)
4. Run `npm link` in the root folder of `waterproof-editor`, this creates a symlink to `waterproof-editor` in the global `node_modules` folder (more info on `npm link` can be found [here](https://docs.npmjs.com/cli/v11/commands/npm-link))
5. Run `npm link @impermeable/waterproof-editor` in the root folder of `waterproof-vscode` this will replace the installed version of `waterproof-editor` by the local version

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
In particular, because this is a regular version, make sure that the version number is of the form
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
