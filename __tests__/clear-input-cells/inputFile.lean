import WaterproofGenre
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

```lean
Example "Example 1"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
intro a b h
use b - a + 1
have x : ℕ := 4
simp
```
:::

```lean
QED
```

```lean
Example "Example 2"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean

```
:::

```lean
QED
```

```lean
Example "Example 3"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```

:::input

```lean
  Fix a : ℝ
  Fix b > 5
  Let's prove that b-a+1 works: b - a + 1 > b - a

```
:::

```lean
QED
```

::::
