-- import Mathlib.Topology.Instances.Real.Defs
import Verbose.English.All

open Verbose English

-- Let’s define mathematical notions here

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- and some nice notation

notation3:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges to " l => sequence_tendsto u l

-- Now configure Verbose Lean
-- (those configuration commands are explained elsewhere)

configureUnfoldableDefs continuous_function_at sequence_tendsto

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros

useDefaultDataProviders

useDefaultSuggestionProviders
