#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";
import copy from "esbuild-plugin-copy";

const watch = process.argv.includes("--watch");
const minify = process.argv.includes("--minify");
const disable_sourcemap = process.argv.includes("--sourcemap=no");
const sourcemap_client = disable_sourcemap ? null : { sourcemap: "inline" };
const sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };

if (watch) console.log("Watch mode enabled, rebuilding on file change...");

const watchPlugin = (fileName) => {
  return {
    name: "log build status",
    setup(build) {
      build.onEnd(result => {
        const errCount = result.errors.length;
        if (errCount > 0) {
          console.error(`❌ Build for ${fileName} failed with ${errCount} error${errCount > 1 ? "s" : ""}`);
        } else {
          console.log(`✅ Build finished for ${fileName}`);
        }
      });
    }
  };
}
  
// Build prosemirror editor.
const fontLoader = "copy";

const editorConfig = {
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
  alias: {
    '@codemirror/autocomplete': './node_modules/@codemirror/autocomplete',
    '@codemirror/commands': './node_modules/@codemirror/commands',
    '@codemirror/language': './node_modules/@codemirror/language',
    '@codemirror/lint': './node_modules/@codemirror/lint',
    '@codemirror/state': './node_modules/@codemirror/state',
    '@codemirror/view': './node_modules/@codemirror/view',
  },
  minify,
  plugins: [watchPlugin("editor")]
};

if (!watch) {
  esbuild.build(editorConfig);
} else {
  const ctx = await esbuild.context(editorConfig);
  ctx.watch();
}

const nodeConfig = {
  entryPoints: ["./src/mainNode.ts"],
  bundle: true,
  ...sourcemap_client,
  format: "cjs",
  platform: "node",
  external: ["vscode"],
  outfile: "out/src/mainNode.js",
  minify,
  loader: {
    ".html": "text",
  },
  plugins: [watchPlugin("extension/node")]
};

// Build of the VS Code extension, for electron (hence cjs + node)
if (!watch) {
  esbuild.build(nodeConfig);
} else {
  const ctx = await esbuild.context(nodeConfig);
  ctx.watch();
}

const browserConfig = {
  entryPoints: ["./src/mainBrowser.ts"],
  bundle: true,
  ...sourcemap_client,
  format: "cjs",
  platform: "browser",
  external: ["vscode", "child_process"],
  outfile: "out/src/mainBrowser.js",
  minify,
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
    watchPlugin("extension/browser"),
  ]
};

// Build browser sources:
if (!watch) {
  esbuild.build(browserConfig);
} else {
  const ctx = await esbuild.context(browserConfig);
  ctx.watch();
}

const viewConfig = (file) => {
  return {
    entryPoints: [file],
    bundle: true,
    ...sourcemap_view,
    platform: "browser",
    outdir: "out",
    outbase: ".",
    minify,
    plugins: [watchPlugin(file)]
  }
};

// Build of the VS Code view, for modern Chrome (webview)
async function viewBuild(file) {
  if (!watch) {
    esbuild.build(viewConfig(file));
  } else {
    const ctx = await esbuild.context(viewConfig(file));
    ctx.watch();
  }
}

viewBuild("./views/goals/index.tsx");
viewBuild("./views/execute/index.tsx");
viewBuild("./views/debug/index.tsx");
viewBuild("./views/help/index.tsx");
viewBuild("./views/search/index.tsx");
viewBuild("./views/symbols/index.tsx");
viewBuild("./views/tactics/index.tsx");
viewBuild("./views/infoview/index.ts");