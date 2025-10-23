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
  Since ?_ we conclude that x + 3 = 3 + x
QED
