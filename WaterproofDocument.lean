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

## ATC - 003

```lean
Example "ATC - 003"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
Fix a : ℝ


```
:::

```lean
QED
```


## ATC - 007

$$`E = mc^2`
```lean

```
```lean

```
```lean

```
```lean

```
```lean

```
```lean

```
```lean

```
```lean

```
```lean
Example "ATC - 007"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
Fix a : ℝ

```
:::

```lean
QED
```

## ATC - 008
```lean
Example "ATC - 008"
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

## ATC - 009
:::hint "Show hint"
  hello
:::
```lean
Example "ATC - 009"
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

## ATC - 010
```lean
--COPY THIS
Example "ATC - 010"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
/-
```

:::input

```lean

```
:::

```lean
-/
QED
```

## ATC - 012
```lean
Example "ATC - 012"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
  Fix a : ℝ
  Fix b > 5
  -- Type on the line below

  We compute
```
:::
```lean
QED
```

## ATC - 013
```lean
Example "ATC - 013"
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

## ATC - 014
```lean
Example "ATC - 014"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu :  u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
```

:::input
```lean
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  By hf applied to ε using that ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  By hu applied to δ using that δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ

```
:::
```lean
QED
```

## ATC - 015

Inline math: $`e^x = 5`.

```lean
Example "ATC - 015"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
  -- Insert a tactic
```
:::
```lean
QED
```

## ATC - 016
```lean
Example "ATC - 016"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```

:::input
```lean
-- Insert a symbol on the line below

```
:::

```lean
QED
```

## ATC - 018
```lean
Example "ATC - 018"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu :  u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
  Proof:
```

:::input
```lean
  -- Type on the line below

  Fix ε > 0
  By hf applied to ε using that ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  By hu applied to δ using that δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ
  exact Hu n n_ge
```
:::
```lean
QED
```

## ATC - 020
```lean
Example "ATC - 020"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```

:::input
```lean
  -- Type 'help' on the line below

```
:::
```lean
QED
```

## ATC - 022

$$`a^2+b^2=c^2`

Markdown

:::hint "Some hint"
Hello
:::

```lean
Example "ATC - 022"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
```
:::input
```lean
  -- help
```
:::
```lean
QED
```

::::
