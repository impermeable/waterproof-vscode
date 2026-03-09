#!/bin/bash
# update-symbols.sh
# Downloads the latest Lean unicode table and regenerates symbols.json
#
# Usage: bash scripts/update-symbols.sh

set -e

# Pinned to release v0.0.224 to avoid breaking changes in the future. Update as needed.
LEAN_URL="https://raw.githubusercontent.com/leanprover/vscode-lean4/v0.0.224/lean4-unicode-input/src/abbreviations.json" 
ABBREV="../completions/lean-abbreviations.json"
OUTPUT="../completions/symbols.json"

echo "Downloading Lean abbreviations..."
curl -fsSL "$LEAN_URL" -o "$ABBREV"

echo "Generating $OUTPUT..."

node generate-symbols.mjs --test


echo "Done."