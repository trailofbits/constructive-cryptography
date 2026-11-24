import Tests.Rendering.Pseudocode
import Tests.Rendering.Widget
import Tests.Rendering.Notation
import Tests.Rendering.TypeNotation

/-!
# Interface fields and source-linked labels

The registered projections must preserve actual alphabets, history predicates and parameters.
Interactive views must retain RPC information for objects, aliases, boundaries and field values.
-/

set_option linter.hashCommand false

open Lean Meta Elab Command Term CCWidget SystemAlgebra DSLExamples
open CategoryTheory

namespace Rendering.InterfaceInfoTests

open SystemAlgebra.DSL in
interface HigherOrder
  apply(f : Bool → Bool) → Bool

open SystemAlgebra.DSL in
interface StructuredAlphabet
  pair(x : Bool × Fin 16) → Unit ⊕ Bool
  empty(x : Fin 0) → Fin 1

elab "assert_interface_projection " t:term " field " symbol:str " equals " expected:term :
    command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some (_, projection, value) := (← interfaceProjections e).find? (·.1 == symbol.getString)
    | throwError "missing interface field {symbol.getString}"
  let wanted ← elabTerm expected (some (← inferType projection))
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq value wanted do throwError "interface field changed: {value}"
  let info ← interfaceOf e
  let some field := info.fields.find? (·.symbol == symbol.getString)
    | throwError "field omitted from presentation"
  unless field.value == (← ppShort value) && field.type == (← ppShort (← inferType projection)) do
    throwError "field's displayed expression or type changed"

assert_interface_projection Counter.outer 3 field "D" equals
  (fun h => h ≠ [] ∧ h.length ≤ 3)
assert_interface_projection BoundedCounter.outer 7 2 field "D" equals
  (fun h => (h ≠ [] ∧ h.length ≤ 7) ∧ h.length ≤ 2)
assert_interface_projection FirstRequests.outer 2 5 field "D" equals
  (fun h => (h ≠ [] ∧ h.length ≤ 5) ∧ h.length ≤ 2)
assert_interface_projection Pad.perPort (fun _ => 4) field "D" equals
  (fun h => h ≠ [] ∧ ∀ i, (restrict i h).length ≤ 4)
assert_interface_projection Interface.tensor (Pad 2) (Cache 5) field "D" equals
  Interface.parallelDomain (Pad 2) (Cache 5)
assert_interface_projection Pad 2 field "X" equals Pad.Input
assert_interface_projection Pad 2 field "Y" equals Pad.Output
assert_interface_projection Interface.unit field "I" equals Empty

-- Hide only explicitly registered constructions, retaining the exact inspected interface.
run_cmd runTermElabM fun _ => do
  for term in #[← `(Counter (budget := 3)),
      ← `(Counter.perPort (budget := fun _ => 3)), ← `(BoundedCounter 7 (budget := 2))] do
    let some (view, codes) ← elabViewCore term true | throwError "missing system view"
    let some iface := view.real.diagram.elem.outer? | throwError "missing interface"
    unless iface.detailsOnly do throwError "expanded interface leaked onto the diagram"
    unless !iface.fields.isEmpty && !iface.ports.isEmpty do
      throwError "compacting the label dropped interface information"
    unless (codeFor? codes view.real.diagram.elem.pos "outer.source").isSome do
      throwError "compacting the label lost the original Lean hover"
    if view.real.diagram.hasWideInterface then
      throwError "an inspected construction still forces a wide diagram"
  let expanded ← elabTerm
    (← `(Interface.tensor
      (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) (Cache 3))) none
  unless (← interfaceOf expanded).detailsOnly do
    throwError "a tensor boundary leaked an expanded interface construction"
  for term in #[← `(Cache 3), ← `(Counter.outer 3),
      ← `(Interface.tensor (Cache 3) (Pad 2))] do
    let iface ← interfaceOf (← elabTerm term none)
    if iface.detailsOnly then throwError "a named interface was unfolded or hidden"
    unless iface.source == (← ppShort (← elabTerm term none)) do
      throwError "the inspector replaced the original interface"

-- Field functions retain their per-port types, including different query/reply alphabets.
run_cmd runTermElabM fun _ => do
  let iface ← elabTerm (← `(Cache 3)) none
  let info ← interfaceOf iface
  unless info.ports.map (·.label) == #["write", "read"] do
    throwError "declared ports changed order or disappeared"
  unless info.ports.map (·.signature) == #["Fin 16 → Fin 16", "Unit → Fin 16"] do
    throwError "incorrect displayed port signatures: {repr info.ports}"
  unless info.ports.map (·.inputNotation) == #["{0,…,15}", "{⋆}"] &&
      info.ports.map (·.outputNotation) == #["{0,…,15}", "{0,…,15}"] do
    throwError "incorrect alphabet notation"
  let query ← mkAppM ``Interface.X #[iface]
  let reply ← mkAppM ``Interface.Y #[iface]
  for (port, queryType, replyType) in
      #[(← `(Cache.Port.write), ← `(Fin 16), ← `(Fin 16)),
        (← `(Cache.Port.read), ← `(Unit), ← `(Fin 16))] do
    let port ← elabTerm port none
    unless ← isDefEq (mkApp query port) (← elabTerm queryType none) do
      throwError "wrong query alphabet"
    unless ← isDefEq (mkApp reply port) (← elabTerm replyType none) do
      throwError "wrong reply alphabet"
  let unrelated ← interfaceOf (mkNatLit 37)
  unless unrelated.fields.isEmpty do throwError "unregistered type acquired a domain"
  let compound ← elabTerm (← `(Interface.tensor (Pad 2) (Cache 5))) none
  unless (← interfacePorts compound).isEmpty do
    throwError "a payload-carrying constructor was treated as a port"
  let higherOrder ← interfaceOf (← elabTerm (← `(HigherOrder 2)) none)
  unless higherOrder.ports.map (·.signature) == #["(Bool → Bool) → Bool"] do
    throwError "function-valued input lost its parentheses"
  unless info.enumerated && (← interfaceOf (← elabTerm (← `(Interface.unit)) none)).enumerated do
    throwError "a complete or empty enumeration was presented as an unresolved family"
  unless !(← interfaceOf compound).enumerated do
    throwError "a sum family was presented as an empty enumeration"
  let restricted ← interfaceOf (← elabTerm (← `(BoundedCounter.outer 7 2)) none)
  let some domainInfo := restricted.fields.find? (·.symbol == "D")
    | throwError "missing domain"
  unless domainInfo.presentation == "{ h | (h ≠ ε ∧ |h| ≤ 7) ∧ |h| ≤ 2 }" do
    throwError "compact domain dropped a restriction: {domainInfo.presentation}"

-- Explicit commands and generic theorem views must keep the local context for every tag.
run_cmd runTermElabM fun _ => do
  let some (j, codes) ← elabViewCore (← `(Counter (budget := 3))) true
    | throwError "system view missing"
  for part in #["", "source", "type", "outer.label", "outer.type", "outer.D.name",
      "outer.D.value", "outer.D.notation", "outer.X.value", "outer.Y.value"] do
    unless (codeFor? codes j.real.diagram.elem.pos part).isSome do
      throwError "missing interactive information: {part}"
  let some (j, codes) ← elabViewCore (← `(Interface.comp_smul)) true
    | throwError "quantified theorem view missing"
  unless (codeFor? codes j.real.diagram.elem.pos "outer.label").isSome do
    throwError "quantified boundary lost its context"
  for part in #["outer.family.port", "outer.family.input", "outer.family.output"] do
    unless (codeFor? codes j.real.diagram.elem.pos part).isSome do
      throwError "symbolic alphabet lost its source information: {part}"
  let some boundary := j.real.diagram.elem.outer? | throwError "missing symbolic interface"
  unless boundary.fields.all (fun f => f.value == f.projection) do
    throwError "an unresolved field lost its registered projection name"

attribute [local cc_diagram "SB"] Rendering.PseudocodeTests.aliasOfSecret

run_cmd runTermElabM fun _ => do
  let e ← elabTerm (← `(Rendering.PseudocodeTests.aliasOfSecret)) none
  unless (← labelFor e) == "SB" do throwError "alias missing"
  let some info := rootCodeInfo? (← Widget.ppExprTagged e)
    | throwError "alias has no root hover information"
  let .ofTermInfo term := info.info.val.info | throwError "alias lost its term information"
  unless term.expr == e do throwError "alias refers to another object"

/-- error: cc_diagram: duplicate interface projections -/
#guard_msgs in
cc_diagram_interface Interface Interface.I Interface.X Interface.X Interface.domain

/-- error: cc_diagram: Prod.fst is not a projection of SystemAlgebra.Interface -/
#guard_msgs in
cc_diagram_interface Interface Prod.fst Interface.X Interface.Y Interface.domain

end Rendering.InterfaceInfoTests
