module

public import ConstructiveCryptography.Notation.Basic
public import RandomSystems.Typed.ParallelAllAttachment
public import RandomSystems.Typed.ParallelAllContext
public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.CryptographicAlgebra.Game
public import ConstructiveCryptography.Tactics.Categorical

/-!
# Notation frontend for interfaces

All notation, `Δ R S`, `R ∥ S`, `R ≃[ε] S`, `𝓡 —[π]→ 𝒮`, `𝓡 —[π; ε]→ 𝒮` and `G |≡ T`, is
defined over the abstract classes in `ConstructiveCryptography.Notation.Basic`, and reads the
selected instances. This module sits above the interface instances and the proof commands and
adds typed serial and tensor notation; on interfaces `Δ` is the transcript distance and `≃[ε]`
quantifies over the `AdmissibleDistinguishers` instance a statement installs. Second
handlers for `Δ` and `∥` (`elabTypedCCDistance`, `elabTypedCCParallel`, sharing
`elabTypedCCOperands`) first read each operand as a typed system on its own interface, so that
attachments such as `Δ (α • R) (α • S)` or `α • R ∥ β • S` infer their interfaces and budgets.
If that fails they restore the elaboration state and defer to the generic handlers, so any
other carrier keeps its own metric and parallel operation. The hints select nothing: both
paths produce the same `distance R S` or `parallel R S`. The
compatibility laws of the distance are restated with `∥` for the `cc_nonexpand` tactic, and
`cc_normalize` applies locality, `(α ⊗ₘ β) • (R ∥ S) = α • R ∥ β • S`, whether the interfaces
are written with `⊗` or with `Interface.tensor`. The categorical action, the direct typed
action and the attachment field of `Interface.resourceTheory` are identified by definitional
bridges, and `cc_parallel_eq` rewrites the abstract `parallel` to `TypedSystem.parallel`, so
all normalize by the same typed laws, also after serial composition or `cc_construct`. Attachment
enters an initial sample, `α • sample P R = sample P (fun s => α • R s)`, for any normalized
law `P`, including nested samples whose laws depend on earlier draws, and acts componentwise on
a finite family, `(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, α k • R k`. A shared draw stays outside the
whole family; normalization never splits it into independent draws of the components:

```text
sample s ← P; ∥ k, R s k    ≠    ∥ k, (sample s ← P; R s k)    in general
```

Serial `α ≫ β` and tensor `α ⊗ₘ β` accept direct `TypedConverter` operands.
`elabTypedCCArrows` tries the selected categorical operation first, and supplies `Interface`
only when neither the operands nor the expected type selects another category.

The named family context uses `TypedConverter.parallelAllContext_smul`:
`parallelAllContext R k • S = ∥ j, Function.update R k S j`. Its fixed components and selected
replacement keep their declared domains; further component equalities remain explicit premises.
Sample hoisting runs after structural attachment, keeping a draw in its owning component.
-/

@[expose] public section

namespace SystemAlgebra

open CategoryTheory CategoryTheory.MonoidalCategory

/-- Serial composition with the same right-associative binding power as categorical `≫`. -/
scoped syntax:80 (name := ccComposition) (priority := high) term:81 " ≫ " term:80 : term

/-- Tensor of arrows with the same right-associative binding power as Mathlib's `⊗ₘ`. -/
scoped syntax:70 (name := ccTensorHom) (priority := high) term:71 " ⊗ₘ " term:70 : term

open Lean Elab Term in
/-- Rewrite directly nested `≫` nodes, including parenthesized ones, to `CategoryStruct.comp`.
One generic attempt covers that chain without re-entering this handler; other operands keep
their syntax. -/
meta partial def ccCompositionGenericSyntax (stx : TSyntax `term) : TermElabM (TSyntax `term) := do
  match stx with
  | `($α ≫ $β) =>
    let α ← ccCompositionGenericSyntax α
    let β ← ccCompositionGenericSyntax β
    `(CategoryTheory.CategoryStruct.comp $α $β)
  | `(($term)) =>
    let term ← ccCompositionGenericSyntax term
    `(($term))
  | _ => return stx

open Lean Elab Term in
/-- Rewrite directly nested `⊗ₘ` nodes, including parenthesized ones, to
`MonoidalCategoryStruct.tensorHom`, as `ccCompositionGenericSyntax` does for `≫`. -/
meta partial def ccTensorGenericSyntax (stx : TSyntax `term) : TermElabM (TSyntax `term) := do
  match stx with
  | `($α ⊗ₘ $β) =>
    let α ← ccTensorGenericSyntax α
    let β ← ccTensorGenericSyntax β
    `(CategoryTheory.MonoidalCategoryStruct.tensorHom $α $β)
  | `(($term)) =>
    let term ← ccTensorGenericSyntax term
    `(($term))
  | _ => return stx

open Lean Meta Elab Term in
/-- Return `some true` for a `Quiver.Hom` over objects other than `Interface`, `some false`
for `Interface` or a non-morphism type, and `none` while the head or object type is unresolved.
Unfold aliases only up to `Quiver.Hom`, before its field reduces to the converter carrier. -/
meta def ccCompositionHasOtherCategory (type : Expr) : TermElabM (Option Bool) := do
  let mut type := (← instantiateMVars type).consumeMData
  while !type.isAppOf ``Quiver.Hom do
    if type.getAppFn.isMVar then return none
    let some unfolded ← unfoldDefinition? type | return some false
    type := unfolded.consumeMData
  let obj ← whnf type.getAppArgs[0]!
  if obj.getAppFn.isMVar then return none
  return some (!obj.isConstOf ``Interface)

open Lean Meta Elab Term in
/-- Inspect the category selected by an operand alone, restoring all state afterward.
The first pass reads selections with pending endpoint capabilities; the second synthesizes
postponed types. An operand that fails alone selects nothing (`some false`). -/
meta def ccCompositionOperandHasOtherCategory
    (stx : TSyntax `term) : TermElabM (Option Bool) := do
  let saved ← saveState
  let generic ← ccCompositionGenericSyntax stx
  try
    try
      let selected ← withoutErrToSorry do
        let term ← elabTerm generic none
        ccCompositionHasOtherCategory (← inferType term)
      if selected == some true then return selected
    catch _ => pure ()
    saved.restore (restoreInfo := true)
    withoutErrToSorry <| withSynthesize do
      let term ← elabTerm generic none
      ccCompositionHasOtherCategory (← inferType term)
  catch _ =>
    return some false
  finally
    saved.restore (restoreInfo := true)

open Lean Elab Term in
/-- Elaborate a binary operation on arrows `α`, `β`. `generic` is the operation of whatever
category and instances the operands and `expectedType?` select. `typed` is the same operation
with only its category fixed to `Interface` and both operands read as `TypedConverter _ _`.

The invariant: `typed` is tried only after `generic` fails, and only if neither
`expectedType?` nor an operand selects another category. Since `typed` names no instance,
composition and tensor remain those in scope.

* The first generic attempt finishes synthesis, so it fails only when this reading fails.
* Every later attempt starts from the saved state, so a discarded reading leaves no
  metavariable assignment or postponed problem behind.
* A selected category keeps the generic reading.
* While the category is unresolved, a generic reading that exposes a category is kept;
  otherwise elaboration postpones, because a later argument may still select a category.
* The typed reading leaves endpoint constraints to the enclosing expression.
* If every attempt fails at once, the first generic error is reported. -/
meta def elabTypedCCArrows
    -- `generic`, `typed` are the two readings of the operation on operands `α`, `β`.
    (generic typed α β : TSyntax `term) (expectedType? : Option Expr) : TermElabM Expr := do
  let saved ← saveState
  try
    withoutErrToSorry <| withSynthesize do
      elabTerm generic expectedType?
  catch genericError =>
    saved.restore (restoreInfo := true)
    let genericOnly : TermElabM Expr := do
      try
        withoutErrToSorry <| elabTerm generic expectedType?
      catch _ =>
        saved.restore (restoreInfo := true)
        throw genericError
    let expectedSelection ← match expectedType? with
      | some type => ccCompositionHasOtherCategory type
      | none => pure (some false)
    let leftSelection ← ccCompositionOperandHasOtherCategory α
    let rightSelection ← ccCompositionOperandHasOtherCategory β
    saved.restore (restoreInfo := true)
    if expectedSelection == some true || leftSelection == some true ||
        rightSelection == some true then
      genericOnly
    else
      if expectedSelection.isNone || leftSelection.isNone || rightSelection.isNone then
        -- Keep the generic category visible while endpoint constraints wait.
        try
          let term ← withoutErrToSorry <| elabTerm generic expectedType?
          if (← ccCompositionHasOtherCategory (← Lean.Meta.inferType term)).isSome then
            return term
        catch _ => pure ()
        saved.restore (restoreInfo := true)
        -- A later argument may still select the category before typed hints are considered.
        tryPostpone
      -- No other category is selected: read both operands as direct converters in Interface.
      try
        withoutErrToSorry <| elabTerm typed expectedType?
      catch _ =>
        saved.restore (restoreInfo := true)
        throw genericError

open Lean Elab Term in
/-- `α ≫ β` by `elabTypedCCArrows`: composition in the selected category, or composition in
`Interface` of direct converters when no other category is selected. -/
@[term_elab ccComposition]
meta def elabTypedCCComposition : TermElab
  -- `α`, `β` are the serial operands; `expectedType?` may determine their outside endpoints.
  | `($α ≫ $β), expectedType? => do
    elabTypedCCArrows (← ccCompositionGenericSyntax (← `($α ≫ $β)))
      (← `(CategoryTheory.CategoryStruct.comp (obj := SystemAlgebra.Interface)
        ($α : TypedConverter _ _) ($β : TypedConverter _ _))) α β expectedType?
  | _, _ => throwUnsupportedSyntax

open Lean Elab Term in
/-- `α ⊗ₘ β` by `elabTypedCCArrows`: the tensor of the selected monoidal structure, or, when no
other category is selected, the tensor in `Interface` of direct converters. -/
@[term_elab ccTensorHom]
meta def elabTypedCCTensorHom : TermElab
  -- `α`, `β` are the tensor operands; `expectedType?` may determine their endpoints.
  | `($α ⊗ₘ $β), expectedType? => do
    elabTypedCCArrows (← ccTensorGenericSyntax (← `($α ⊗ₘ $β)))
      (← `(CategoryTheory.MonoidalCategoryStruct.tensorHom (C := SystemAlgebra.Interface)
        ($α : TypedConverter _ _) ($β : TypedConverter _ _))) α β expectedType?
  | _, _ => throwUnsupportedSyntax

open Lean Elab Term in
/-- Elaborate `operation (R : TypedSystem _) (S : TypedSystem _)` for a binary CC operation
(`distance` or `parallel`), the two `_` being independent interfaces. The carrier is then
known before attachments in `R`, `S` are elaborated, so their outside interfaces are inferred.
Elaboration errors are not turned into `sorry`, so a failure is visible here; the saved state
is then restored and the syntax is passed on to the generic handler. The result is the
selected `operation` itself; the hints choose no metric, action or parallel instance. -/
meta def elabTypedCCOperands (operation R S : TSyntax `term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let saved ← saveState
  try
    withoutErrToSorry <| withSynthesize do
      elabTerm (← `($operation
        ($R : TypedSystem _) ($S : TypedSystem _))) expectedType?
  catch _ =>
    saved.restore
    throwUnsupportedSyntax

open Lean Elab Term in
/-- `Δ R S` with typed carrier hints (`elabTypedCCOperands`); the metric is the selected one. -/
@[term_elab ccDistance]
meta def elabTypedCCDistance : TermElab
  | `(Δ $R $S), expectedType? => do
    elabTypedCCOperands (← `(ConstructiveCryptography.CryptographicAlgebra.distance))
      R S expectedType?
  | _, _ => throwUnsupportedSyntax

open Lean Elab Term in
/-- `R ∥ S` with typed carrier hints (`elabTypedCCOperands`), one interface per ordered
component; the parallel operation is the selected one. -/
@[term_elab ccParallel]
meta def elabTypedCCParallel : TermElab
  | `($R ∥ $S), expectedType? => do
    elabTypedCCOperands (← `(ConstructiveCryptography.CryptographicAlgebra.parallel))
      R S expectedType?
  | _, _ => throwUnsupportedSyntax

namespace Interface

attribute [cc_normalization] comp_smul identity_attach

-- Definitional bridges, below the laws' default priority: the categorical action and the
-- `resourceTheory` attachment field left by `cc_construct` are rewritten to `α • R` with
-- `α : TypedConverter A B`, and the abstract `parallel` to `TypedSystem.parallel`, where the
-- typed laws below apply.
attribute [cc_normalization 100] smul_eq_typed_smul attach_eq_typed_smul cc_parallel_eq

-- The typed laws: `(α ≫ β) • R = α • (β • R)`, `id • R = R`, binary and finite-family
-- locality, and `α • sample P R = sample P (fun s => α • R s)`. None moves an initial sample
-- into independent component draws, so a draw around the whole assembly stays shared.
attribute [cc_normalization]
  TypedConverter.comp_smul
  TypedConverter.identity_attach
  TypedConverter.parallel_attach
  TypedConverter.parallelAll_attach
  TypedConverter.parallelAllContext_smul

-- Hoist samples after structural attachment, so serial composition exposes a component's owner.
attribute [cc_normalization 900] TypedConverter.smul_sample

lemma tensor_smul {A B C D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : TypedSystem B) (S : TypedSystem D) :
    (α ⊗ₘ β) • (R ∥ S) = (α • R) ∥ (β • S) :=
  ConstructiveCryptography.CryptographicAlgebra.attach_parallel
    α β R S

open Lean Meta Simp in
/-- `tensor_smul` whatever the spelling of the interfaces: the action of `α ⊗ₘ β` on `R ∥ S`,
with its types written through `⊗` or through `Interface.tensor`, is `α • R ∥ β • S`. The
two spellings agree only up to unfolding the monoidal structure, which `simp` does not do, so
the rule is keyed on the action alone and matches its arguments here. -/
simproc [cc_normalization] tensorSmul (@HSMul.hSMul _ _ _ _ _ _) := fun e => do
  let_expr HSMul.hSMul _ _ _ _ f x := e | return .continue
  let_expr MonoidalCategoryStruct.tensorHom _ _ _ A B C D α β := f | return .continue
  let_expr TypedSystem.parallel _ _ R S := x | return .continue
  let proof := mkAppN (mkConst ``tensor_smul) #[A, B, C, D, α, β, R, S]
  let_expr Eq _ lhs rhs := ← inferType proof | return .continue
  unless ← withDefault (isDefEq e lhs) do return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint proof (← mkEq e rhs)) }

lemma distance_smul_le {A B : Interface} (α : A ⟶ B) (R S : TypedSystem B) :
    Δ (α • R) (α • S) ≤ Δ R S :=
  ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
    α R S

/-- Opposite typed attachments that exchange two system pairs preserve their distance: for
`forward : A ⟶ B` and `backward : B ⟶ A`, the four equalities `forward • R = R'`,
`forward • S = S'`, `backward • R' = R` and `backward • S' = S` give `Δ R' S' = Δ R S`.
The interface form of `distance_eq_of_mutual_attach`; Maurer--Renner 2016, Definition 2
(printed p. 11): “d(αR, αS) ≤ d(R, S) for all α”. -/
lemma distance_eq_of_mutual_smul {A B : Interface}
    (forward : A ⟶ B) (backward : B ⟶ A)
    (R S : TypedSystem B) (R' S' : TypedSystem A)
    (hforwardR : forward • R = R') (hforwardS : forward • S = S')
    (hbackwardR : backward • R' = R) (hbackwardS : backward • S' = S) :
    Δ R' S' = Δ R S :=
  ConstructiveCryptography.CryptographicAlgebra.distance_eq_of_mutual_attach
    forward backward R S R' S' hforwardR hforwardS hbackwardR hbackwardS

/-- The hybrid inequality, with both endpoints inferred from the goal. -/
lemma distance_triangle {A : Interface} {R T : TypedSystem A} (S : TypedSystem A) :
    Δ R T ≤ Δ R S + Δ S T :=
  ConstructiveCryptography.CryptographicAlgebra.distance_triangle
    R S T

lemma distance_parallel_left_le {A B : Interface}
    (R S : TypedSystem A) (T : TypedSystem B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le
    R S T

lemma distance_parallel_right_le {A B : Interface}
    (R : TypedSystem A) (S T : TypedSystem B) : Δ (R ∥ S) (R ∥ T) ≤ Δ S T :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le
    R S T

lemma distance_parallel_le {A B : Interface}
    (R S : TypedSystem A) (T U : TypedSystem B) :
    Δ (R ∥ T) (S ∥ U) ≤ Δ R S + Δ T U :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le
    R S T U

end Interface

-- The compatibility laws, stated with the concrete parallel composition.
-- Reducible-only matching avoids unfolding probabilities on inapplicable rules.
scoped macro_rules
  | `(tactic| cc_nonexpand) => `(tactic|
      first
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le" =>
          Interface.distance_parallel_left_le _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le" =>
          Interface.distance_parallel_right_le _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le" =>
          Interface.distance_parallel_le _ _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_attach_le" =>
          Interface.distance_smul_le _ _ _)

end SystemAlgebra
