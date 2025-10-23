import WaterproofLikeWdget
open ProofWidgets

Example "Reflexivity of equality"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x = x
Proof:
  with_panel_widgets [GoalTypePanel]
  Fix x
  Since ?_ we conclude that x = x
QED

Example "Reflexivity 2"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x + 3 = 3 + x
Proof:
  with_panel_widgets [GoalTypePanel]
  Fix x
  We compute
QED

Example "Combining quantifiers"
  Given:
  Assume:
  Conclusion: ∀ a : ℝ, ∀ b > 5, ∃ c, c > b - a
Proof:
  with_panel_widgets [GoalTypePanel]
  Fix a : ℝ
  Fix b > 5
  Let's prove that b - a + 1 works
  We compute
QED
