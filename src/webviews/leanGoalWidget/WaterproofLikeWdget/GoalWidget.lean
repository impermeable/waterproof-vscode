import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel
open ProofWidgets Jsx

@[expr_presenter]
def presenter : ExprPresenter where
  userName := "Just goal"
  layoutKind := .inline
  present e :=
    return <span>
      <br /><b  style={json% {color: "#569cd6", fontSize: "16px"}}>We need to show:</b><br /><br />
      <br /><InteractiveCode fmt={← Lean.Widget.ppExprTagged e} /><br />
    </span>
