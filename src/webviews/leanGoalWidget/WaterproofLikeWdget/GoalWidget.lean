import ProofWidgets
import ProofWidgets.Component.Panel.GoalTypePanel
open Lean Server ProofWidgets Jsx


@[server_rpc_method]
def GoalsPanel.rpc (p : ProofWidgets.PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let inner : Html :=
      match p.goals[0]? with
        | some g => <span><InteractiveCode fmt={g.type} /></span>
        | none => <span>No goals here</span>
    return <details «open»={true} id={"goals-panel"}>
        <summary className="mv2 pointer">Goals</summary>
        <div className="ml1">{inner}</div>
      </details>
@[widget_module]
def GoalsPanel : Component ProofWidgets.PanelWidgetProps :=
  mk_rpc_widget% GoalsPanel.rpc

show_panel_widgets [GoalsPanel]
