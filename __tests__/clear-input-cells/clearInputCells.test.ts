import { clearInputCells } from "../../src/helpers/exerciseSheet";
import * as path from "path";
import * as fs from "fs";

/**
 * This test file tests the function that removes code from input cells of waterproof lean and rocq files.
 */

it("should remove content of every input cell of waterproof rocq code", () => {
  runTest("inputFile.mv", "outputFile.mv", ".mv");
});

it("should preserve the language identifier in .mv files (rocq and coq)", () => {
  runTest("inputFileMixedRocqCoq.mv", "outputFileMixedRocqCoq.mv", ".mv");
});

it("should remove content of every input cell of waterproof lean code", () => {
  runTest("inputFile.lean", "outputFile.lean", ".lean");
});

function runTest(
  inputFilePath: string,
  expectedOutputFilePath: string,
  ext: string,
) {
  const inputPath = path.join(__dirname, inputFilePath);
  const inputText: string = fs.readFileSync(inputPath, "utf-8");
  const outputPath = path.join(__dirname, expectedOutputFilePath);
  const outputText: string = fs.readFileSync(outputPath, "utf-8");
  const result = clearInputCells(inputText, ext);
  expect(result).toBe(outputText);
}
