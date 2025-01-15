// @ts-check

import eslint from '@eslint/js';
import tseslint from 'typescript-eslint';

const config = tseslint.config(
  {
    ignores: ["editor_output/", "out/", "test_out/"],
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