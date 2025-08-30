// @ts-check

import eslint from '@eslint/js';
import tseslint from 'typescript-eslint';

const config = tseslint.config(
  {
    ignores: ["editor_output/", "vendor", "out/", "test_out/", "lib", "*.config.js", "esbuild*.mjs", "scripts/"],
  },
  {
   extends: [
     eslint.configs.recommended,
     tseslint.configs.recommended,
   ],
   rules: {
       "@typescript-eslint/no-unused-vars": ["error", {
         "varsIgnorePattern": "^_",
         "argsIgnorePattern": "^_"
       }],
     },
  }
);
export default config;