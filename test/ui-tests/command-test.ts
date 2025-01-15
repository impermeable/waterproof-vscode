import { ActivityBar, EditorView, SideBarView, WebView, Workbench } from "vscode-extension-tester";

// TODO: Do these tests actually test something?

describe('Set up extension', () => {

    it('start coqnitive', async () => {
        const prompt = await new Workbench().openCommandPrompt();
        await prompt.setText('>coqnitive.start');
        await prompt.confirm();
    }).timeout(10000);

});


describe('Side Panel Button Test', () => {
    it('open side panel', async() => {
        new SideBarView();
        const sidepanel = await new ActivityBar().getViewControl('Waterproof');
        if (sidepanel) { await sidepanel.openView();};
    }).timeout(10000);

})

describe('common execute', () => {
    it('open common execute', async() => {
        await new EditorView().openEditor("CommonExecute", 1);
        const webview = await new WebView();
        webview.switchToFrame();
    })
})

describe('symbols', () => {
    it('open symbols', async() => {
        await new EditorView().openEditor("Symbols", 1);
        const webview = await new WebView();
        webview.switchToFrame();
    })
})

