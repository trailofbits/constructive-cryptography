import ProofWidgets.Component.Basic

/-! Temporary hover inspectors, with explicit double-click pinning and outside-click dismissal.
The same controller serves native Lean widgets and standalone HTML exports. -/

namespace CCWidget
open Lean ProofWidgets

structure InspectorProps where
  label : String
  identity : String := ""
  symbol : String := "ⓘ"
  deriving Server.RpcEncodable

/-- Fixed UI code, independent of all expression-derived text. -/
def inspectorController : String := include_str "inspector.js"

/-- The standalone binding uses the same controller without a React or network dependency. -/
def exportedInspectorJavascript : String :=
  inspectorController ++ "\nenhanceExportedInspectors();\n"

@[widget_module]
def Inspector : Component InspectorProps where
  javascript := inspectorController ++ "
    import * as React from 'react';
    const e = React.createElement;
    export default function Inspector(props) {
      const button = React.useRef(null), popup = React.useRef(null);
      const id = React.useId();
      React.useEffect(() => attachInspector(button.current, popup.current), [props.identity]);
      return e('span', {className:'cc-inspector'},
        e('button', {ref:button, type:'button', className:'cc-inspector-trigger',
          'aria-label':props.label, 'aria-expanded':false, 'aria-controls':id,
          'aria-haspopup':'dialog'}, props.symbol ?? 'ⓘ'),
        e('div', {id, ref:popup, popover:'auto', role:'dialog',
          'aria-label':props.label, className:'cc-inspector-body'},
          e('button', {type:'button', className:'cc-inspector-close',
            'aria-label':'Close information'}, '×'), props.children));
    }"

end CCWidget
