#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";

// Running the build without watching
async function main() {
    var browser = build("./src/mainBrowser.ts","out/src/mainBrowser.js","browser");
    var node = build("./src/mainNode.ts","out/src/mainNode.js", "node");
    var infoView = viewBuild("./views/goals/index.tsx");
    var logView = viewBuild("./views/logbook/index.tsx");
    var executeView = viewBuild("./views/execute/index.tsx");
    var helpView = viewBuild("./views/help/index.tsx");
    var searchView = viewBuild("./views/search/index.tsx");
    var expandDefinitionView = viewBuild("./views/expandDefinition/index.tsx");
    var symbolsView = viewBuild("./views/symbols/index.tsx");
    var tacticView = viewBuild("./views/tactics/index.tsx");

	const fontLoader = "copy";
    var editor = esbuild.build({
		entryPoints: ["./editor/src/index.ts"],
		bundle: true,
		outdir: "./editor_output",
	  	platform: "browser",
	  	loader: {
			".woff": fontLoader,
			".woff2": fontLoader,
			".ttf": fontLoader,
		},
	}).then(() => {
	  console.log("Build finished for ./editor/src/index.ts");
	}).catch(() => {
	  process.exit(1);
	});

    await Promise.all([node, browser, editor, infoView, logView, executeView, helpView, searchView, expandDefinitionView, symbolsView]);
}

async function build(input, output, platform) {
    return esbuild
        .build({
        entryPoints: [input],
        bundle: true,
        format: "cjs",
        platform: platform,
        external: ["vscode"],
        outfile: output,
        loader: {
            ".html": "text",
        }
        })
        .then(() => {
        console.log("Build finished for " + input);
        })
        .catch(() => process.exit(1));
}

// Build of the VS Code view, for modern Chrome (webview)
function viewBuild(file) {
    return esbuild
      .build({
        entryPoints: [file],
        bundle: true,
        platform: "browser",
        outdir: "out",
        outbase: ".",
      })
      .then(() => {
        console.log(`Build finished for ${file}`);
      })
      .catch(() => process.exit(1));
}

main();
