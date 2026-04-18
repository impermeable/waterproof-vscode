import * as path from 'path';
import * as fs from 'fs';
import { topLevelBlocksLean } from '../../editor/src/document-construction/lean';


/**
 * This test file aims at testing functionality of splitting waterproof lean document into a list of blocks.
 */


it('should put preamble ending with "#doc ... =>" as the first block, but without the "#doc ... =>" line itself', () => {
    const expectedOutput = `import WaterproofGenre
import Verbose.English.All
open Verbose English

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

notation:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation:50 u:80 " converges to " l => sequence_tendsto u l
`;

    const inputPath = path.join(__dirname, 'input.lean');
    const input: string = fs.readFileSync(inputPath, 'utf-8');
    const outputDocument = topLevelBlocksLean(input);
    expect(outputDocument[0].stringContent).toBe(expectedOutput);
})
