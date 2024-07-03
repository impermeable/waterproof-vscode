#!/bin/bash
npm run lezer-generator
npx esbuild --bundle --platform=node --outfile=out.js parser-debug-tool.mjs
node out.js
