/** @type {import('ts-jest').JestConfigWithTsJest} */
module.exports = {
  preset: "ts-jest",
  testEnvironment: "node",
  rootDir: "./",
  roots: ["<rootDir>"],
  modulePaths: ["<rootDir>"],
  moduleDirectories: ["node_modules"],
  transform: {
    "^.+\\.[tj]sx?$": [
      "ts-jest",
      {
        tsconfig: "tsconfig.jest.json",
      },
    ],
  },
  testPathIgnorePatterns: ["/node_modules/", "/__helpers__/"],
  transformIgnorePatterns: [
    "node_modules/(?!(@impermeable|@codemirror|@lezer|prosemirror-model|prosemirror-transform|prosemirror-schema-list|orderedmap|crelt|w3c-keyname|style-mod)/)",
  ],
};
