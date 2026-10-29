import ConstructiveCryptography.Notation.Basic
import RandomSystems.Typed.ParallelAllAttachment
import ConstructiveCryptography.InterfaceAlgebra
import ConstructiveCryptography.CryptographicAlgebra.Game
import ConstructiveCryptography.Tactics.Categorical

/-!
# Notation for interfaces

Scoped notation for the CC operations on interfaces: `S —[α]→ T` and `S —[α; ε]→ T` for exact
and approximate construction, and `G |≡ T` for conditional equivalence of a game to a typed
system. The generic `Δ R S`, `R ∥ S` and `R ≃[ε] S` come from
`ConstructiveCryptography.Notation.Basic`; on interfaces `Δ` is the transcript distance and
`≃[ε]` quantifies over the `AdmissibleDistinguishers` instance a statement installs. Second
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
-/

namespace SystemAlgebra

open CategoryTheory CategoryTheory.MonoidalCategory

open Lean Elab Term in
/-- Elaborate `operation (R : TypedSystem _) (S : TypedSystem _)` for a binary CC operation
(`distance` or `parallel`), the two `_` being independent interfaces. The carrier is then
known before attachments in `R`, `S` are elaborated, so their outside interfaces are inferred.
Elaboration errors are not turned into `sorry`, so a failure is visible here; the saved state
is then restored and the syntax is passed on to the generic handler. The result is the
selected `operation` itself; the hints choose no metric, action or parallel instance. -/
def elabTypedCCOperands (operation R S : TSyntax `term)
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
def elabTypedCCDistance : TermElab
  | `(Δ $R $S), expectedType? => do
    elabTypedCCOperands (← `(ConstructiveCryptography.CryptographicAlgebra.distance))
      R S expectedType?
  | _, _ => throwUnsupportedSyntax

open Lean Elab Term in
/-- `R ∥ S` with typed carrier hints (`elabTypedCCOperands`), one interface per ordered
component; the parallel operation is the selected one. -/
@[term_elab ccParallel]
def elabTypedCCParallel : TermElab
  | `($R ∥ $S), expectedType? => do
    elabTypedCCOperands (← `(ConstructiveCryptography.CryptographicAlgebra.parallel))
      R S expectedType?
  | _, _ => throwUnsupportedSyntax

scoped notation:50 source " —[" converter "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
    converter source target

scoped notation:50 source " —[" converter "; " error "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
    converter source target error

/-- Conditional equivalence `G |≡ T` of a game to a typed system (CR18, Definition 4.19): the
field of `DistinctionGames`. -/
scoped notation:50 G:51 " |≡ " T:51 =>
  ConstructiveCryptography.DistinctionGames.ConditionallyEquivalent G T

namespace Interface

attribute [cc_normalization] comp_smul identity_attach

-- Definitional bridges, below the laws' default priority: the categorical action and the
-- `resourceTheory` attachment field left by `cc_construct` are rewritten to `α • R` with
-- `α : TypedConverter A B`, and the abstract `parallel` to `TypedSystem.parallel`, where the
-- typed laws below apply.
attribute [cc_normalization 100] smul_eq_typed_smul attach_eq_typed_smul cc_parallel_eq

-- The typed laws: `(α ≫ β) • R = α • (β • R)`, `id • R = R`, binary and finite-family
-- locality, and `α • sample P R = sample P (fun s => α • R s)`. None moves an initial sample
-- into a component, so a shared draw stays shared.
attribute [cc_normalization]
  TypedConverter.comp_smul
  TypedConverter.identity_attach
  TypedConverter.parallel_attach
  TypedConverter.smul_sample
  TypedConverter.parallelAll_attach

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
