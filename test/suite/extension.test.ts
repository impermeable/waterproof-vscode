import * as assert from 'assert';
import { after } from 'mocha';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as vscode from 'vscode';
import { IStatusComponent } from '../../src/components';
import { CoqnitiveStatusBar } from '../../src/components/enableButton';



suite('Extension Test Suite', () => {
  after(() => {
    vscode.window.showInformationMessage('All tests done!');
  });
  let extensionContext: vscode.ExtensionContext;

  test('Test enable button', async () => {
    const button: IStatusComponent = new CoqnitiveStatusBar;
    
    //var kroStatusItem = vscode.window.createStatusBarItem("coqnitive.enable");
    //assert.strictEqual(kroStatusItem.text, "Coqnitive (activating)");

  });
});