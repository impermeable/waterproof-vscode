import { group } from "console";
import { ActivityBar, Button, By, EditorView, SideBarView, ViewControl, WebDriver, WebView, Workbench } from "vscode-extension-tester";
import { CoqEditorProvider } from "../../src/pm-editor";


describe('Set up extension', () => {

    it('start coqnitive', async () => {
        const prompt = await new Workbench().openCommandPrompt();
        await prompt.setText('>coqnitive.start');
        await prompt.confirm();
    }).timeout(10000);

});


describe('Side Panel Button Test', () => {
    it('open side panel', async() => {
        const view = new SideBarView();
        const sidepanel = await new ActivityBar().getViewControl('Waterproof');
        if (sidepanel) { const view1 = await sidepanel.openView();};
    }).timeout(10000);

})

describe('common execute', () => {
    it('open common execute', async() => {
        const webb = await new EditorView().openEditor("CommonExecute", 1);
        const webview = await new WebView();
        webview.switchToFrame();
    })
})

describe('symbols', () => {
    it('open symbols', async() => {
        const webb = await new EditorView().openEditor("Symbols", 1);
        const webview = await new WebView();
        webview.switchToFrame();
    })
})

