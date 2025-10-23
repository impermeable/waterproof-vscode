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

Example "Using cases to prove max"
  Given:
  Assume:
  Conclusion: ∀ (x y: ℝ), (max x y) = x ∨ (max x y) = y
Proof:
  with_panel_widgets [GoalTypePanel]
  Fix x y
  We proceed using cases on the comparison between x and y:
    Case 1: x > y
      Since x > y we have (max x y) = x
    Case 2: x ≤ y
      Since x ≤ y we have (max x y) = y
QED

Example "Using cases to prove max"
  Given:
  Assume:
  Conclusion: ∀ (x y: ℝ), (max x y) = x ∨ (max x y) = y
Proof:
  with_panel_widgets [GoalTypePanel]
  Fix x y
  We discuss depending on whether x ≥ y ∨ x < y
    Assume h : x ≥ y
    Let's prove that (max x y) = x
      Since x ≥ y we have (max x y) = x
    Assume x < y
    Let's prove that (max x y) = y
      Since x < y we have (max x y) = y

  Consider cases on whether x ≥ y:
    Since h we have that max x y = x
  else
    Since ¬h we have max x y = y
QED
