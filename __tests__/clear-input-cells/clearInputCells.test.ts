import { clearInputCells } from "../../src/helpers/exerciseSheet";
import * as path from "path";
import * as fs from "fs";

/**
 * This test file tests the function that removes code from input cells of waterproof lean and rocq files.
 */

it("should remove content of every input cell of waterproof rocq code", () => {
  const inputPath = path.join(__dirname, "inputFile.mv");
  const input: string = fs.readFileSync(inputPath, "utf-8");
  const outputPath = path.join(__dirname, "outputFile.mv");
  const output: string = fs.readFileSync(outputPath, "utf-8");
  const result = clearInputCells(input, ".mv");
  expect(result).toBe(output);
});

it("should remove content of every input cell of waterproof lean code", () => {
  const inputPath = path.join(__dirname, "inputFile.lean");
  const input: string = fs.readFileSync(inputPath, "utf-8");
  const outputPath = path.join(__dirname, "outputFile.lean");
  const output: string = fs.readFileSync(outputPath, "utf-8");
  const result = clearInputCells(input, ".lean");
  expect(result).toBe(output);
});
