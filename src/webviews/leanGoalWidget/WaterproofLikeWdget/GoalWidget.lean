import ProofWidgets
import ProofWidgets.Component.Panel.GoalTypePanel
open Lean Server ProofWidgets Jsx

@[server_rpc_method]
def GoalsPanel.rpc (p : ProofWidgets.PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let inner : Html :=
      -- Check if any goals are present at the location
      match p.goals[0]? with
        -- .type returns the CodeWithInfos type that is suited for pretty printing
        | some g =>
          <div>
            <h3  style={json% {color: "#569cd6", fontSize: "16px"}}>We need to show</h3>
            <span><InteractiveCode fmt={g.type} /></span>
          </div>
        | none => <h3 style={json% {color: "#569cd6", fontSize: "16px"}}>No goals here</h3>
    return <details «open»={true} id={"goals-panel"}>
        <summary className="mv2 pointer">Goals</summary>
        <div className="ml1">{inner}</div>
      </details>

@[widget_module]
def GoalsPanel : Component ProofWidgets.PanelWidgetProps :=
  mk_rpc_widget% GoalsPanel.rpc

show_panel_widgets [GoalsPanel]
