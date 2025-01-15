import * as path from 'path';

import { runTests } from '@vscode/test-electron';
import { ExTester, SetupOptions } from 'vscode-extension-tester';
import { version } from 'os';

// Run all testing programs
async function main() {
	await baseTests();
	await uiTests();
}

async function baseTests() {
	try {
		// The folder containing the Extension Manifest package.json
		// Passed to `--extensionDevelopmentPath`
		const extensionDevelopmentPath = path.resolve(__dirname, '../');

		// The path to the extension test runner script
		// Passed to --extensionTestsPath
		const extensionTestsPath = path.resolve(__dirname, './suite/index');

		// Download VS Code, unzip it and run the integration test
		await runTests({ extensionDevelopmentPath, extensionTestsPath });
	} catch (err) {
		console.error(err);
		console.error('Failed to run base tests');
		process.exit(1);
	}
}

async function uiTests() {
	try {
		const tester: ExTester = new ExTester(".ui-test");
		console.log("Maybe succes");
		const code = tester.downloadCode();
		const chrome = tester.downloadChromeDriver();
		await Promise.all([code, chrome]);
		await tester.installVsix({ vsixFile: "test_out/extension.vsix"});
		return tester.runTests("test_out/test/ui-tests/**/*.js").then( (number) => {
			if (number) console.log("Failed mocha tests with number " + number);
		});
	} catch (err) {
		console.error(err);
		console.error('Failed to run ui tests');
		process.exit(1);
	}
}

main();