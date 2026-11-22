module

public import ConstructiveCryptography.Tactics.Substitution
public import ConstructiveCryptography.Notation

/-!
# A two-step substitution argument

The compact calculation follows the displayed chain:

    X = α • R₀ ≃ₛ α • R₁ = β • S₁ ≃ₛ β • S₀ = Y.

Here • is the existing converter attachment; ≃ₛ is local notation for the
explicitly selected substitution relation, not equality or a new relation.
Inside cc_calc, ≃ denotes that same selected relation. The common converter is
inferred from the written endpoints; ← explicitly reverses the second premise.
All three exact equalities are supplied.

Statistical distance bounds are separate hypotheses, not consequences of
computational substitution. The companion calculation adds those bounds.
The generated implication-witness and use-count examples live in
Tests.Substitution.Tactics; the raw regressions
remain in Tests.Substitution.Implication. Direct typed converters below check that every
statistical line keeps the outside carrier and the goal's selected metric.

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.Substitution.Calculation

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

universe u v w

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi] {A B : C}
variable (relation : SubstitutionRelation C)

local infix:50 " ≃ₛ " => relation.substitutes _

/-- [1, Section 2.3.1, p. 15]: "we explicitly show the implication
by the following sequence of steps". The calculation keeps each supplied
transformation, orientation, and exact join visible. -/
lemma substitutes_of_two_steps
    (R₀ R₁ S₀ S₁ : Phi B) (X Y : Phi A)
    (α β : A ⟶ B)
    (hR : R₀ ≃ₛ R₁) (hS : S₀ ≃ₛ S₁)
    (start : X = α • R₀) (join : α • R₁ = β • S₁)
    (finish : Y = β • S₀) : X ≃ₛ Y := by
  cc_calc relation
    X = α • R₀ := start
    _ ≃ α • R₁ := hR
    _ = β • S₁ := join
    _ ≃ β • S₀ := ← hS
    _ = Y := finish.symm

local notation "d" => distance

/-- [1, Section 2.3.1, p. 15]: "we then collect the sum of such
pᵢ's into a value ε". This companion uses separately supplied statistical
bounds; it does not infer them from the substitution premises. -/
lemma distance_two_steps_le [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    (R₀ R₁ S₀ S₁ : Phi B) (X Y : Phi A)
    (α β : A ⟶ B) (ε₁ ε₂ : ENNReal)
    (hR : d R₀ R₁ ≤ ε₁) (hS : d S₀ S₁ ≤ ε₂)
    (start : X = α • R₀) (join : α • R₁ = β • S₁)
    (finish : Y = β • S₀) : d X Y ≤ ε₁ + ε₂ := by
  cc_calc statistical
    X = α • R₀ := start
    _ ≈[ε₁] α • R₁ := hR
    _ = β • S₁ := join
    _ ≈[ε₂] β • S₀ := ← hS
    _ = Y := finish.symm

#print axioms substitutes_of_two_steps
#print axioms distance_two_steps_le

end Tests.Substitution.Calculation

namespace Tests.Substitution.TypedCalculation

open SystemAlgebra
open scoped SystemAlgebra NNReal

variable
  -- `A` is the outside interface; `B` is the interface of the compared components.
  {A B : Interface} (α : TypedConverter A B) (R S : TypedSystem B)
  -- `ε` bounds the component distance by `bound`.
  (ε : ℝ≥0) (bound : Δ R S ≤ ε)

include bound

/-- One supplied component bound transports through the displayed converter `α`. -/
lemma attachment_distance_le : Δ (α • R) (α • S) ≤ ε := by
  cc_calc statistical
    α • R ≈[ε] α • S := bound

/-- Exact changes of presentation surround one component replacement, with no extra error. -/
lemma presentation_distance_le
    -- `X`, `Y` present the attached components through `left_eq`, `right_eq`.
    (X Y : TypedSystem A) (left_eq : X = α • R) (right_eq : α • S = Y) :
    Δ X Y ≤ ε := by
  cc_calc statistical
    X = α • R := left_eq
    _ ≈[ε] α • S := bound
    _ = Y := right_eq

/-- Local introductions and named assemblies keep the same carrier at omitted endpoints. -/
example : ∀ X Y : TypedSystem A, X = α • R → α • S = Y → Δ X Y ≤ ε := by
  intro X Y left_eq right_eq
  let C := α
  cc_calc statistical
    _ = C • R := left_eq
    _ ≈[ε] C • S := bound
    _ = _ := right_eq

/-- A local name for the distance retains the goal's selected metric. -/
example : let d := fun X Y : TypedSystem A => Δ X Y
    d (α • R) (α • S) ≤ ε := by
  intro d
  cc_calc statistical
    α • R ≈[ε] α • S := bound

/-- A bound on unrelated components cannot justify the displayed replacement. -/
example (T U : TypedSystem B) (_unrelated : Δ T U ≤ ε) : Δ (α • R) (α • S) ≤ ε := by
  fail_if_success
    cc_calc statistical
      α • R ≈[ε] α • S := _unrelated
  exact attachment_distance_le α R S ε bound

/-- A separately selected action needs its own bound; canonical attachment supplies none. -/
example [otherAction : HSMul (TypedConverter A B) (TypedSystem B) (TypedSystem A)]
    (outerBound : Δ (α • R) (α • S) ≤ ε) : Δ (α • R) (α • S) ≤ ε := by
  fail_if_success
    cc_calc statistical
      α • R ≈[ε] α • S := bound
  cc_calc statistical
    α • R ≈[ε] α • S := outerBound

#print axioms attachment_distance_le
#print axioms presentation_distance_le

end Tests.Substitution.TypedCalculation
