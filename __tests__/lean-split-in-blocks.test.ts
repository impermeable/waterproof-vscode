import { topLevelBlocksLean } from '../editor/src/document-construction/lean';


/**
 * This test file aims at testing functionality of splitting waterproof lean document into a list of blocks.
 */

const input = `import WaterproofGenre
import Verbose.English.All
open Verbose English

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

notation:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation:50 u:80 " converges to " l => sequence_tendsto u l

#doc (WaterproofGenre) "Index" =>
::::multilean

## ATC - 003

\`\`\`lean
Example "ATC - 003"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
\`\`\`
:::input
\`\`\`lean
intro a b h
use b - a + 1
have x : ℕ := 4
simp
\`\`\`
:::

\`\`\`lean
QED
\`\`\`

::::`;

const firstBlock = `import WaterproofGenre
import Verbose.English.All
open Verbose English

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

notation:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation:50 u:80 " converges to " l => sequence_tendsto u l
`;

it('should put preamble ending with "#doc ... =>" as the first block, but "#doc ... =>" line should not be visible', () => {
    const outputDocument = topLevelBlocksLean(input);
    // Check that the visible part of the first block is preamble without "#doc ... =>"
    expect(outputDocument[0].stringContent).toBe(firstBlock);
    // Check that the second block does not contain "#doc ... =>" line either
    expect(outputDocument[1].stringContent).not.toContain('#doc (WaterproofGenre) "Index" =>');
})
