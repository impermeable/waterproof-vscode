import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel
open ProofWidgets Jsx

@[expr_presenter]
def presenter : ExprPresenter where
  userName := "Just goal"
  layoutKind := .inline
  present e :=
    return <span>
      <b>We need to show:</b><br /><br />
      <InteractiveCode fmt={← Lean.Widget.ppExprTagged e} />
    </span>
