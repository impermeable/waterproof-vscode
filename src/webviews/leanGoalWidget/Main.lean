import WaterproofLikeWdget



Example "Reflexivity of equality"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x = x
Proof:
  Fix x
  We compute
QED

Example "Reflexivity 2"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x + 3 = 3 + x
Proof:
  Fix x
  We compute
QED

Example "Combining quantifiers"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
  Fix a : ℝ
  Fix b > 5
  Let's prove that b - a + 1 works
  We compute
QED

-- Example "Using cases to prove max"
--   Given: (x y : ℝ)
--   Assume: (h : x ≤ y ∨ x > y)
--   Conclusion: max x y = x ∨ max x y = y
-- Proof:
-- QED
