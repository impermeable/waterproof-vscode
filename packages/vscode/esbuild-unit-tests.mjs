#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";

esbuild.build({
    entryPoints: ["__tests__/mvFileToProsemirror.test.ts", "__tests__/parser.test.ts"],
    outdir: "./__tests_output__",
    platform: "browser",
})
.then(() => {console.log("Finished building __tests__");})
.catch(() => {process.exit(1);});
