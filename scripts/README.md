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

`completions/symbols+lean.json` is a committed, generated file combining the hand-curated `symbols.json` with Lean's unicode abbreviation table.

To update it (e.g. after a new Lean release), run:
```bash
bash update-symbols.sh
```
This downloads the abbreviations from the pinned Lean release tag, regenerates `symbols+lean.json`, and runs a diff test against the base.

To regenerate without re-downloading:
```bash
node generate-symbols.mjs --test
```