import Rendering
import Tests.RevealedHCoefficient
import Examples.DSL.Components

/-!
Proof views preserve explicit witness fields, oriented uses, exact joins and per-position errors.
No premise becomes established by viewing a chain. Opaque and symbolic objects stay inspectable.
-/

open Lean Meta Elab Command Term CCWidget ProofWidgets
open CategoryTheory ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SubstitutionRelation SystemAlgebra DSLExamples

namespace Rendering.ProofTests

/-- Complete elaboration before testing the presentation of an expression. -/
def elaborateProof (term : Syntax.Term) : TermElabM Expr := do
  let e ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Static serialization checks determinism and escaping without forcing native RPC references. -/
def proofHtml (e : Expr) : MetaM String := do
  let some body ← proofViewHtml? e false | throwError "missing proof view"
  match staticHtml (proofPanel body) with
  | .ok text => return text
  | .error err => throwError "{err}"

elab "assert_proof " term:term " positions " n:num : command => runTermElabM fun _ => do
  let e ← elaborateProof term
  let some () ← withProofView e fun view => do
    unless view.original == e do throwError "proof view changed its source"
    unless view.positions.size == n.getNat do throwError "wrong number of positions"
    for position in view.positions do
      unless ← withoutModifyingState <| isDefEq (← inferType position.left)
          (← inferType position.right) do throwError "a position changed interface"
    | throwError "missing registered proof view"
  let first ← proofHtml e
  unless first == (← proofHtml e) do throwError "nondeterministic proof view"

section Chains
variable {C : Type} [Category C] [CategoryTheory.MonoidalCategory C]
variable {Phi : C → Type} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A : C} (worlds : Bool → Phi A)

def roundTrip : Implication (fun _ : Unit => A) (fun _ => worlds) A 1 :=
  let one := Implication.single (systems := fun _ : Unit => worlds) () false (𝟙 A)
  one.append one.reverse rfl

/-- A named identity remains a named component in a witness projection. -/
def namedConverter : A ⟶ A := 𝟙 A

assert_proof roundTrip worlds positions 2
assert_proof (roundTrip worlds).reverse positions 2

-- Equal assumption names do not merge positions or their different error budgets.
variable (loss : Fin 2 → ENNReal)
variable (localBound : ∀ j : Fin 2, distance (worlds false) (worlds true) ≤ loss j)
assert_proof (roundTrip worlds).distance_le loss localBound positions 2
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `((roundTrip worlds).distance_le loss localBound))
  let some () ← withProofView e fun view => do
    unless view.conclusion?.isSome && view.theorem?.isSome do
      throwError "registered application lost its conclusion"
    for p in view.positions do
      unless p.error?.isSome && p.premise?.isSome do throwError "a position lost its actual bound"
    unless ← isDefEq view.positions[0]!.assumption.value view.positions[1]!.assumption.value do
      throwError "the repeated assumption changed"
    unless view.positions[0]!.direction.value.isConstOf ``Bool.false do
      throwError "the first direction changed"
    unless view.positions[1]!.direction.value.isConstOf ``Bool.true do
      throwError "the reversed direction changed"
    for p in view.positions do
      unless p.converter.value.isAppOf ``CategoryTheory.CategoryStruct.id do
        throwError "finite selection obscured the identity converter: {p.converter.value}"
    | throwError "missing chain"
  let bare ← elaborateProof (← `(roundTrip worlds))
  let some () ← withProofView bare fun view => do
    unless view.conclusion?.isNone && view.positions.all (·.error?.isNone) do
      throwError "a bare chain acquired a conclusion or error bound"
    | throwError "missing bare chain"

run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(Implication.single (systems := fun _ : Unit => worlds)
    () false (namedConverter (A := A))))
  let some () ← withProofView e fun view => do
    unless view.positions[0]!.converter.value.isAppOf ``namedConverter do
      throwError "a named converter was unfolded"
    | throwError "missing named-converter chain"

-- Logical premises use assumption names, even when a name is used at several positions.
variable (relation : SubstitutionRelation C (Phi := Phi))
variable (premise : ∀ _ : Unit, relation.substitutes A (worlds false) (worlds true))
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(Implication.substitutes relation (roundTrip worlds) premise))
  let some () ← withProofView e fun view => do
    for p in view.positions do
      let some proof := p.premise? | throwError "logical premise missing"
      unless proof.getAppArgs.back! == p.assumption.value do
        throwError "a logical premise was indexed by position"
      let _ ← inferType proof
      unless p.error?.isNone do throwError "a logical premise acquired a scalar error"
    | throwError "missing logical chain"

-- Symbolic and long families stay symbolic; no invented number of displayed uses.
variable {n : Nat} (symbolic : Implication (fun _ : Unit => A) (fun _ => worlds) A n)
variable (longChain : Implication (fun _ : Unit => A) (fun _ => worlds) A 100)
assert_proof symbolic positions 1
assert_proof longChain positions 1
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(symbolic))
  let some () ← withProofView e fun view => do
    unless view.index?.isSome do throwError "symbolic chain lost its index binder"
    | throwError "missing symbolic chain"

-- An unrelated proof that mentions a witness is not classified as the witness's technique.
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(Eq.refl (roundTrip worlds)))
  unless (← withProofView e fun _ => pure ()).isNone do
    throwError "an unrelated theorem application acquired a technique"
end Chains

section HCoefficient
variable {A : Interface} (R S : TypedSystem A) (ε : NNReal)
variable (w : RandomSystem.HCoefficient R.1 S.1 ε)
assert_proof w positions 0
assert_proof Interface.distance_le_of_hCoefficient w positions 0
-- Raw systems retain their alphabets and domain without acquiring a typed interface.
variable (rawReal rawIdeal : RandomSystem (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain)
variable (rawArgument : RandomSystem.HCoefficient rawReal rawIdeal 3)
assert_proof rawArgument positions 0
assert_proof SystemAlgebra.Tests.RevealedHCoefficient.halfBadReveal
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3)
  (Counter (budget := 3)) positions 0
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(w))
  let html ← proofHtml e
  unless (html.splitOn "class=\"cc-h-budget\"").length == 1 do
    throwError "a coercion duplicated the symbolic budget"
  let some () ← withProofView e fun view => do
    unless view.title == "H-coefficient" && view.groups.size == 5 do
      throwError "missing technique fields"
    let fields := view.groups.flatMap fun g => g.fields
    for name in #[``RandomSystem.HCoefficient.sample, ``RandomSystem.HCoefficient.realReveal,
        ``RandomSystem.HCoefficient.idealReveal, ``RandomSystem.HCoefficient.ratio,
        ``RandomSystem.HCoefficient.bound] do
      unless fields.any (·.source.isAppOf name) do throwError "missing original field {name}"
    unless view.conclusion?.isNone do
      throwError "bare witness was turned into a theorem application"
    | throwError "missing H-coefficient view"
  -- Cast-dependent fields stay symbolic in the argument and exact in the source inspector.
  let castWitness ← elaborateProof (← `(SystemAlgebra.Tests.RevealedHCoefficient.halfBadReveal
    (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3) (Counter (budget := 3))))
  let html ← proofHtml castWitness
  unless (html.splitOn "cc-h-method").length > 1 do
    throwError "missing transcript argument presentation"
  unless (html.splitOn ">Projection<").length == 1 do
    throwError "record projection disclosures returned to the main argument"
  for label in #["Replies", "Normalization", "Expected error"] do
    unless (html.splitOn label).length > 1 do
      throwError "a proof field lost its label: {label}"

-- Signed budgets retain the actual positive-part conversion in the raw distance theorem.
variable (signed : RandomSystem.HCoefficient R.1 S.1 (-3))
assert_proof signed.transcriptDistance_le S.2 positions 0
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(signed.transcriptDistance_le S.2))
  let html ← proofHtml e
  unless (html.splitOn "ENNReal.ofReal").length > 1 do
    throwError "a signed error lost its positive-part conversion"

-- The compact equations must reject a substituted budget rather than printing the old formula.
run_cmd runTermElabM fun _ => do
  let e ← elaborateProof (← `(w))
  let some () ← withProofView e fun v => do
    let some s := v.transcript? | throwError "missing transcript schema"
    let altered := v.parameters.set! 2 { v.parameters[2]! with
      value := ← mkNumeral (← inferType v.parameters[2]!.value) 3 }
    let rendered ← observing? (renderTranscriptArgument (proofRenderContext false)
      { v with parameters := altered } s)
    unless rendered.isNone do throwError "a changed error budget kept the old compact formula"
    let swapped := v.parameters.set! 0 { v.parameters[0]! with value := v.parameters[1]!.value }
    let rendered ← observing? (renderTranscriptArgument (proofRenderContext false)
      { v with parameters := swapped } s)
    unless rendered.isNone do throwError "a swapped real system kept the old mixture equation"
    | throwError "missing transcript view"
end HCoefficient

-- Partial registrations, unresolved terms and misleading names acquire no proof view.
run_cmd runTermElabM fun _ => do
  for term in #[← `(17), ← `(Interface.distance_le_of_hCoefficient),
      ← `(fun (HCoefficient : Nat) => HCoefficient)] do
    let e ← elabTerm term none
    unless (← withProofView e fun _ => pure ()).isNone do throwError "unrecognized proof classified"
  let hole ← mkFreshExprMVar (mkConst ``True)
  let html ← proofJustification (proofRenderContext false) hole
  let .ok source := staticHtml html | throwError "unfinished evidence was not exportable"
  unless (source.splitOn "Unfinished").length > 1 do throwError "an open goal looked finished"

end Rendering.ProofTests
