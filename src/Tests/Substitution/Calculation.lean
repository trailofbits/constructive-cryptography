import ConstructiveCryptography.Tactics.Substitution

set_option autoImplicit false

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
remain in Tests.Substitution.Implication.
-/

namespace Tests.Substitution.Calculation

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

universe u v w

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi] {A B : C}
variable (relation : SubstitutionRelation C)

local infix:50 " ≃ₛ " => relation.substitutes _

/-- Banfi, Section 2.3.1 (printed p. 15): "we explicitly show the implication
by the following sequence of steps". The calculation keeps each supplied
transformation, orientation, and exact join visible. -/
theorem substitutes_of_two_steps
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

/-- Banfi, Section 2.3.1 (printed p. 15): "we then collect the sum of such
pᵢ's into a value ε". This companion uses separately supplied statistical
bounds; it does not infer them from the substitution premises. -/
theorem distance_two_steps_le [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
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
