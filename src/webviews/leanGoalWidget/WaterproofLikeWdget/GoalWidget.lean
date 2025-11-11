import ProofWidgets
-- import ProofWidgets.Component.Panel.SelectionPanel
open Lean Server ProofWidgets Jsx


@[server_rpc_method]
def GoalsPanel.rpc (p : ProofWidgets.PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let inner : Html :=
      match p.goals[0]? with
        | some g => <span>{.text g.type.pretty}</span>  -- or g.type.plainText
        | none => <span>No goals here</span>
    return <details «open»={true} id={"goals-panel"}>
        <summary className="mv2 pointer">Goals</summary>
        {inner}
      </details>

@[widget_module]
def GoalsPanel : Component ProofWidgets.PanelWidgetProps :=
  mk_rpc_widget% GoalsPanel.rpc

show_panel_widgets [GoalsPanel]
