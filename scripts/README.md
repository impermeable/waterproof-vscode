# Scripts

This folder contains some scripts used to generate the Waterproof tactics sheets.

Running 
```bash
node createmd.js
```
Creates the [`tactics-sheet.md`](../docs/tactics-sheet.md) file in the [`../docs`](../docs) folder. 

### Pandoc
Running the following command in the [`../docs`](../docs) folder converts the Markdown file into a webpage
```bash
pandoc tactics-sheet.md -o tactics-sheet.html
```

Running the following command in the [`../docs`](../docs) folder converts the Markdown file into a pdf file
```bash
pandoc tactics-sheet.md -o tactics-sheet.pdf --pdf-engine=lualatex -V 'monofont:DejaVu Sans Mono' -V 'mainfont:DejaVu Sans'
```

### Symbol generation

`completions/symbols+lean.json` is a generated file combining the hand-curated `symbols.json` with Lean's unicode abbreviation table. It is produced automatically at build time and is not committed to git.

The Lean abbreviation table comes from the `@leanprover/unicode-input` npm package, pinned to an exact version in `package.json`.

To update the Lean table (e.g. after a new Lean release), bump the version in `package.json` and run:
```bash
npm install
```

To regenerate manually:
```bash
npm run generate-symbols
```

To regenerate and run test/show reports:
```bash
npm run generate-symbols -- --test
```