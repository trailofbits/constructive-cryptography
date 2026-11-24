import Rendering.Widget
import ConstructiveCryptography.CryptographicAlgebra.Epsilon

/-! Regression tests for the semantic projection, using the actual typed CC
surface. These checks run during elaboration and do not add logical axioms. -/

-- These tests deliberately retain the commands that drive the infoview.
set_option linter.hashCommand false

open Lean Meta Elab Command Term CCWidget
open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

namespace Rendering.Tests

partial def shape : Diagram → String
  | .atom e => e.source
  | .attach _ c r _ => s!"attach({shape c},{shape r})"
  | .parallel _ l r => s!"parallel({shape l},{shape r})"
  | .serial _ l r => s!"serial({shape l},{shape r})"
  | .tensor _ l r => s!"tensor({shape l},{shape r})"
  | .wrapper e _ => s!"wrapper({e.source})"

/-- Every projected node must point to its exact original subterm. -/
partial def checkPositions (root : Expr) (d : Diagram) : MetaM Unit := do
  let actual ← viewSubexpr (fun _ sub => ppShort sub)
    (SubExpr.Pos.ofArray d.elem.pos) root
  unless actual == d.elem.source do
    throwError "incorrect source path: {d.elem.source} points to {actual}"
  match d with
  | .atom _ => pure ()
  | .attach _ l r _ | .parallel _ l r | .serial _ l r | .tensor _ l r =>
    checkPositions root l
    checkPositions root r
  | .wrapper _ b => checkPositions root b

elab "assert_diagram " t:term " shape " expected:str : command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let d ← parseDiagram e
  unless shape d == expected.getString do
    throwError "expected {expected.getString}, got {shape d}"
  checkPositions e d
  -- A second projection of the same elaborated expression is byte-for-byte equal.
  unless (toJson d).compress == (toJson (← parseDiagram e)).compress do
    throwError "projection is not deterministic"

elab "assert_comparison " t:term " relation " expected:str : command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let some j ← parseJudgment? e | throwError "comparison not recognized"
  unless j.rel == expected.getString && j.bridge?.isSome do
    throwError "comparison relation changed"
  unless j.source == (← ppShort e) do throwError "statement changed"

variable {C : Type} [Category C] [MonoidalCategory C]
variable {Phi : C → Type} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A B D E : C}
variable (c : A ⟶ B) (d : B ⟶ D) (e : A ⟶ E)
variable (R : Phi D) (S : Phi E) (T : Phi A)

assert_diagram c • (d • R) shape "attach(c,attach(d,R))"
assert_diagram (c ≫ d) • R shape "attach(serial(c,d),R)"
assert_diagram parallel (Phi := Phi) (parallel (Phi := Phi) R S) T
  shape "parallel(parallel(R,S),T)"
assert_diagram parallel (Phi := Phi) R (parallel (Phi := Phi) S T)
  shape "parallel(R,parallel(S,T))"
assert_diagram (d ⊗ₘ e) • parallel (Phi := Phi) R S
  shape "attach(tensor(d,e),parallel(R,S))"

-- Arbitrary scalar multiplication and products carry no CC role.
assert_diagram (2 • (3 : Nat)) shape "2 • 3"
assert_diagram (2 * (3 : Nat)) shape "2 * 3"

variable (simulator : A ⟶ D) (ε : ENNReal)
assert_diagram simulator • R shape "attach(simulator,R)"
assert_comparison distance (Phi := Phi) R R = ε relation "="
assert_comparison distance (Phi := Phi) R R ≤ ε relation "≤"
assert_comparison distance (Phi := Phi) R R < ε relation "<"

#guard_msgs in
#cc_diagram_check (attach_serial (Phi := Phi) c d R)
#guard_msgs in
#cc_diagram_check Specification.Constructs (Phi := Phi) d
  ({R} : ConstructiveCryptography.Specification (Phi D))
  ({d • R} : ConstructiveCryptography.Specification (Phi B))
#guard_msgs in
#cc_diagram_check Specification.ConstructsWithin (Phi := Phi) d
  ({R} : ConstructiveCryptography.Specification (Phi D))
  ({d • R} : ConstructiveCryptography.Specification (Phi B)) ε

-- Existentials retain their quantifier; no witness or simulator is fabricated.
/-- error: cc_diagram: expression not recognized -/
#guard_msgs in
#cc_diagram_check (∃ n : Nat, n = 0)

/-- error: cc_diagram: expression not recognized -/
#guard_msgs in
#cc_diagram_check (2 • (3 : Nat) = 6)

-- Even when a known head is partially applied, it is not an attachment.
run_cmd runTermElabM fun _ => do
  let n := ``ConstructiveCryptography.CryptographicAlgebra.attach
  let e ← mkConstWithFreshMVarLevels n
  unless (← declRole? e).isNone do throwError "partial application was recognized"

-- Constant labels use exact names. An applied constant retains its arguments.
namespace First
def item : Nat := 7
end First
namespace Second
def item : Nat := 9
end Second
attribute [cc_diagram "first"] First.item
run_cmd runTermElabM fun _ => do
  unless (← labelFor (mkConst ``First.item)) == "first" do throwError "exact label lost"
  unless (← labelFor (mkConst ``Second.item)) != "first" do throwError "label leaked by suffix"

/-- The argument must remain visible even when the head has a display alias. -/
def labeledFunction (n : Nat) : Nat := n
attribute [cc_diagram "alias"] labeledFunction
assert_diagram labeledFunction 2 shape "labeledFunction 2"
run_cmd runTermElabM fun _ => do
  let e ← elabTerm (← `(labeledFunction 2)) none
  unless (← labelFor e) == "alias 2" do
    throwError "applied nickname lost its argument: {← labelFor e}"

#print axioms ConstructiveCryptography.CryptographicAlgebra.attach_serial
#print axioms ConstructiveCryptography.CryptographicAlgebra.attach_parallel

end Rendering.Tests

namespace Rendering.Adversarial
open Rendering.Tests
variable {C : Type} [Category C] [MonoidalCategory C]
variable {Phi : C → Type} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A B D : C} (c : A ⟶ B) (d : B ⟶ D)
variable (R : Phi D) (S : Phi B) (T : Phi A)
variable (ε δ : ENNReal)

-- Identities, associators, unknown applications, and scalar arithmetic stay visible.
assert_diagram (𝟙 D) • R shape "attach(𝟙 D,R)"
assert_diagram parallel (Phi := Phi) S R shape "parallel(S,R)"
assert_diagram c • (𝟙 B) • d • R shape "attach(c,attach(𝟙 B,attach(d,R)))"
assert_diagram Specification.map (Phi := Phi) d
  ({R} : ConstructiveCryptography.Specification (Phi D))
  shape "attach(d,{R})"
assert_comparison distance (Phi := Phi) R R = 0 relation "="
assert_comparison distance (Phi := Phi) R R ≤ (ε + δ) relation "≤"
assert_comparison distance (Phi := Phi) R R ≤ (⊤ : ENNReal) relation "≤"

-- Source and target relaxations are not stripped, summed, or treated as witnesses.
#guard_msgs in
#cc_diagram_check Specification.Constructs (Phi := Phi) d
  (Specification.epsilonRelaxation (Phi := Phi) ε
    ({R} : ConstructiveCryptography.Specification (Phi D)))
  (Specification.epsilonRelaxation (Phi := Phi) δ
    ({S} : ConstructiveCryptography.Specification (Phi B)))

elab "assert_boundaries " t:term : command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let d ← parseDiagram (← instantiateMVars e)
  let .attach _ (.atom converter) (.atom _) _ := d | throwError "unexpected shape"
  unless converter.kind == .conv do throwError "converter acquired an unsupported role"
  let some (.literal "A" _) := converter.outer?.map Iface.label
    | throwError "exposed interface lost"
  let some (.literal "B" _) := converter.inner?.map Iface.label | throwError "used interface lost"

variable (simulator Eve adversary : A ⟶ B)
assert_boundaries simulator • S
assert_boundaries Eve • S
assert_boundaries adversary • S

/-- A named system does not authorize looking inside its definition. -/
def namedSystem {C : Type} [Category C] {Phi : C → Type} [ResourceTheory C Phi]
    {A B : C} (c : A ⟶ B) (S : Phi B) : Phi A := attach c S
assert_diagram namedSystem c S shape "namedSystem c S"

-- A depth budget preserves the entire opaque subterm, never an ellipsis.
elab "assert_depth_fallback " t:term : command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let .atom el ← parseDiagram e (depth := 0) | throwError "depth limit did not stop"
  unless el.source == (← ppShort e) do throwError "depth fallback discarded information"
assert_depth_fallback c • d • R

-- A branch type is not copied from a neighbouring branch or inferred from its name.
elab "assert_tensor_boundaries " t:term : command => runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let .parallel root (.atom l) (.atom r) ← parseDiagram (← instantiateMVars e)
    | throwError "parallel structure lost"
  let some (.tensor (.literal "D" _) (.literal "B" _)) := root.outer?.map Iface.label
    | throwError "aggregate interface lost its ordered tensor"
  let some (.literal "D" _) := l.outer?.map Iface.label | throwError "left interface changed"
  let some (.literal "B" _) := r.outer?.map Iface.label | throwError "right interface changed"
assert_tensor_boundaries parallel (Phi := Phi) R S

/-- error: cc_diagram: invalid argument positions for
ConstructiveCryptography.ResourceTheory.attach (arity 8) -/
#guard_msgs (whitespace := lax) in
cc_diagram_application ConstructiveCryptography.CryptographicAlgebra.attach 99 0

/-- error: cc_diagram: invalid argument positions for
ConstructiveCryptography.ResourceTheory.attach (arity 8) -/
#guard_msgs (whitespace := lax) in
cc_diagram_application ConstructiveCryptography.CryptographicAlgebra.attach 0 0

/-- error: cc_diagram: conflicting role for ConstructiveCryptography.ResourceTheory.attach -/
#guard_msgs in
cc_diagram_parallel ConstructiveCryptography.ResourceTheory.attach 1 0

end Rendering.Adversarial

namespace Rendering.Unrelated
open Rendering.Tests

elab "assert_unrecognized " t:term : command => runTermElabM fun _ => do
  unless (← elabView t).isNone do throwError "unrelated expression received a CC meaning"

-- Neither an arbitrary family nor an arbitrary category is a CC capability.
variable {X : Type} [Category X] {F : X → Type} {A B D : X}
variable (R : F A) (f : A ⟶ B) (g : B ⟶ D)
assert_unrecognized R
assert_unrecognized f
assert_unrecognized f ≫ g
assert_unrecognized f = f
assert_unrecognized ({R} : Set (F A))

end Rendering.Unrelated

namespace Rendering.AlternativeCategory
open Rendering.Unrelated
variable {C : Type} {Phi : C → Type}
variable [first : Category C] [@ResourceTheory C first Phi]
variable [second : Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

-- The same interface type with a different category is a distinct structure.
assert_unrecognized f
assert_unrecognized f ≫ g

end Rendering.AlternativeCategory
