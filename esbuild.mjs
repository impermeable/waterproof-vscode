#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";
import copy from "esbuild-plugin-copy";

let watchConfig = (entry) => {
  return {
    onRebuild(error, result) {
      console.log(`[watch] build started (rebuild for ${entry})`);
      if (error) {
        error.errors.forEach((error) =>
          console.error(
            `> ${error.location.file}:${error.location.line}:${error.location.column}: error: ${error.text}`
          )
        );
      } else console.log(`[watch] build finished (rebuild for ${entry}`);
    },
  };
};

let watch = process.argv.includes("--watch") ? watchConfig : (entry) => false;
let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap_client = disable_sourcemap ? null : { sourcemap: "inline" };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

// Build prosemirror editor.
const fontLoader = "copy";

var editor = esbuild.build({
	entryPoints: ["./editor/src/index.ts"],
	bundle: true,
	outdir: "./editor_output",
  ...sourcemap_client,
  platform: "browser",
  loader: {
		".woff": fontLoader,
		".woff2": fontLoader,
		".ttf": fontLoader,
    ".grammar": "file"
	},
  minify,
  watch: watch("./editor/src/index.ts")
}).then(() => {
  console.log("[watch] build finished for ./editor/src/index.ts");
}).catch(() => {
  process.exit(1);
});

// Build of the VS Code extension, for electron (hence cjs + node)
var node = esbuild
  .build({
    entryPoints: ["./src/mainNode.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "node",
    external: ["vscode"],
    outfile: "out/src/mainNode.js",
    minify,
    watch: watch("./src/mainNode.ts"),
    loader: {
      ".html": "text",
    }
  })
  .then(() => {
    console.log("[watch] build finished for ./src/mainNode.ts");
  })
  .catch(() => process.exit(1));

var browser = esbuild
  .build({
    entryPoints: ["./src/mainBrowser.ts"],
    bundle: true,
    ...sourcemap_client,
    format: "cjs",
    platform: "browser",
    external: ["vscode", "child_process"],
    outfile: "out/src/mainBrowser.js",
    minify,
    watch: watch("./src/mainBrowser.ts"),
    loader: {
      ".html": "text",
    },
    plugins: [
      copy({
        assets: {
          from: ['./vendor/*.zip', './vendor/*.bc', './vendor/*.js', './vendor/*.wasm'],
          to: ['..'],
        },
        keepStructure: false,
      }),
    ],
  })
  .then(() => {
    console.log("[watch] build finished for ./src/mainBrowser.ts");
  })
  .catch(() => process.exit(1));

// Build of the VS Code view, for modern Chrome (webview)
function viewBuild(file) {
  return esbuild
    .build({
      entryPoints: [file],
      bundle: true,
      ...sourcemap_view,
      platform: "browser",
      outdir: "out",
      outbase: ".",
      minify,
      watch: watch(file),
    })
    .then(() => {
      console.log(`[watch] build finished for ${file}`);
    })
    .catch(() => process.exit(1));
}

var infoView = viewBuild("./views/goals/index.tsx");
var executeView = viewBuild("./views/execute/index.tsx");
var debugView = viewBuild("./views/debug/index.tsx");
var helpView = viewBuild("./views/help/index.tsx");
var searchView = viewBuild("./views/search/index.tsx");
var expandDefinitionView = viewBuild("./views/expandDefinition/index.tsx");
var symbolsView = viewBuild("./views/symbols/index.tsx");
var executeView = viewBuild("./views/execute/index.tsx");
var tacticsView = viewBuild("./views/tactics/index.tsx");


