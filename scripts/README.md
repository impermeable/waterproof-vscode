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

Running the following command in the [`../docs`](../docs) folder converts the Markdown file into a pdf file (see [../docs/tactics-sheet.pdf](../docs/tactics-sheet.pdf))
```bash
pandoc tactics-sheet.md -o tactics-sheet.pdf --pdf-engine=lualatex -V 'monofont:DejaVu Sans Mono' -V 'mainfont:DejaVu Sans'
```