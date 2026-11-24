import Tests.Rendering.Interfaces

/-! Display names change labels only: arguments, interfaces, source and node positions survive. -/

open Lean Meta Elab Command Term CCWidget SystemAlgebra DSLExamples CategoryTheory

namespace Rendering.LabelTests

/-- Finish implicit arguments before inspecting the expression that the widget will receive. -/
def elaborated (term : Syntax.Term) : TermElabM Expr := do
  let e ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

elab "assert_display " term:term " as " expected:str : command => runTermElabM fun _ => do
  let e ← elaborated term
  let d ← parseDiagram e
  unless d.elem.label == expected.getString do
    throwError "expected display {expected.getString}, got {d.elem.label}"
  unless d.elem.source == (← ppShort e) do throwError "display name replaced the Lean source"
  Rendering.Tests.checkPositions e d
  unless (toJson d).compress == (toJson (← parseDiagram e)).compress do
    throwError "display naming is not deterministic"

-- The interface argument is redundant in the identity node, but stays in its actual type.
assert_display 𝟙 (Cache 3) as "𝟙"
assert_display TypedConverter.id (Cache 3) as "𝟙"
assert_display id (3 : Nat) as "id 3"
run_cmd runTermElabM fun _ => do
  let e ← elaborated (← `(𝟙 (Cache 3)))
  let d ← parseDiagram e
  unless d.elem.kind == .conv do throwError "identity lost its converter role: {repr d.elem}"
  for iface in #[d.elem.outer?, d.elem.inner?] do
    let some iface := iface | throwError "identity lost an interface"
    unless iface.source == (← ppShort (← elaborated (← `(Cache 3)))) && iface.ports.size == 2 do
      throwError "identity lost its actual interface or ports"
  let partialId ← mkConstWithFreshMVarLevels ``CategoryTheory.CategoryStruct.id
  unless (← declRole? partialId).isNone do throwError "partial identity was abbreviated"

section DeclarationNames
attribute [local cc_diagram "BC"] DSLExamples.BoundedCounter
attribute [local cc_diagram "CacheI"] DSLExamples.Cache
assert_display BoundedCounter 7 (budget := 2) as "BC 7"
assert_display BoundedCounter 9 (budget := 2) as "BC 9"
run_cmd runTermElabM fun _ => do
  let source ← elaborated (← `(Cache 3))
  let iface ← interfaceOf source
  unless (match iface.label with | .literal "CacheI 3" _ => true | _ => false) do
    throwError "interface nickname or applied argument lost"
  unless iface.source == (← ppShort source) do throwError "interface nickname changed the source"
  let compound ← elaborated (← `(Interface.tensor (Cache 3) (Cache 4)))
  let some (.tensor (.literal "CacheI 3" _) (.literal "CacheI 4" _)) :=
      some (← interfaceOf compound).label
    | throwError "a tensor interface lost its component nicknames"
end DeclarationNames

section ExactNames
local cc_diagram_name "Counter₃" := Counter (budget := 3)
assert_display Counter (budget := 3) as "Counter₃"
assert_display Counter (budget := 4) as "Counter"
assert_display Counter (budget := 3 + 0) as "Counter"

local cc_diagram_name "I₃" :=
  Interface.queryBudget Counter.Port Counter.Input Counter.Output 3
run_cmd runTermElabM fun _ => do
  let some (j, codes) ← elabViewCore (← `(Counter (budget := 3))) true
    | throwError "named system lost its view"
  let some iface := j.real.diagram.elem.outer? | throwError "named system lost its interface"
  unless (match iface.label with | .literal "I₃" _ => true | _ => false) &&
      !iface.detailsOnly && iface.ports.size == 2 do
    throwError "an explicit interface name was hidden or lost its port data"
  for part in #["", "source", "type", "outer.label", "outer.source", "outer.D.value"] do
    unless (codeFor? codes j.real.diagram.elem.pos part).isSome do
      throwError "display name lost native Lean information: {part}"
  let compound ← elaborated (← `(Interface.tensor
    (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) (Cache 3)))
  let compoundInfo ← interfaceOf compound
  if compoundInfo.detailsOnly then throwError "a tensor hid an explicitly named interface"
  unless (match compoundInfo.label with
    | .tensor (.literal "I₃" _) _ => true | _ => false) do
    throwError "the name of a tensor component disappeared"

section Override
local cc_diagram_name "Temporary" := Counter (budget := 3)
assert_display Counter (budget := 3) as "Temporary"
end Override
assert_display Counter (budget := 3) as "Counter₃"

local cc_diagram_name "pass" := 𝟙 (Cache 3)
assert_display 𝟙 (Cache 3) as "pass"
assert_display 𝟙 (Cache 4) as "𝟙"

local cc_diagram_name "Independent bits" :=
  TypedSystem.parallel (FreshBits (budget := 3)) (SecretBit (budget := 3))
run_cmd runTermElabM fun _ => do
  let e ← elaborated
    (← `(TypedSystem.parallel (FreshBits (budget := 3)) (SecretBit (budget := 3))))
  let d ← parseDiagram e
  let .parallel elem _ _ := d | throwError "a display name concealed the parallel operation"
  unless elem.named && elem.label == "Independent bits" do throwError "composite name missing"
  let .ok html := staticHtml (renderDiagram d #[] #[]) | throwError "named composite export failed"
  unless (html.splitOn "Independent bits").length > 1 do
    throwError "composite name was not displayed"
  Rendering.Tests.checkPositions e d

local cc_diagram_name "<img src=x onerror=alert(1)>" := Counter (budget := 11)
run_cmd runTermElabM fun _ => do
  let some j ← elabView (← `(Counter (budget := 11))) | throwError "named view missing"
  let .ok html := staticHtml (panel (renderJudgment j #[])) | throwError "named export failed"
  unless (html.splitOn "<img").length == 1 && (html.splitOn "&lt;img").length > 1 do
    throwError "display name was interpreted as HTML"
end ExactNames
assert_display Counter (budget := 3) as "Counter"

/-- error: cc_diagram_name: the display name must not be empty -/
#guard_msgs in
cc_diagram_name "  " := Counter (budget := 3)

section OpenTerm
variable (q : Nat)
/-- error: cc_diagram_name: use a closed expression with all types and universes fixed -/
#guard_msgs in
cc_diagram_name "C" := Counter (budget := q)
end OpenTerm

/-- A small import fixture for persistence of exact-expression display metadata. -/
def exportedLabelTarget : Nat := 17
cc_diagram_name "Seventeen" := exportedLabelTarget

end Rendering.LabelTests
