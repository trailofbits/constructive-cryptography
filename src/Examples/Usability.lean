import ConstructiveCryptography.Notation

/-!
# Proof commands on interfaces

The CC notation and proof commands on arbitrary interfaces: normalization of attachment and
parallel composition (`cc_normalize`), non-expansion (`cc_nonexpand`), the triangle
inequality (`cc_triangle`), and exact construction (`cc_construct`).
-/

namespace SystemAlgebra.Usability

open CategoryTheory CategoryTheory.MonoidalCategory
open Interface
open scoped SystemAlgebra

variable {A B C : Interface}

example (α : A ⟶ B) (β : B ⟶ C) (R : Resource C) :
    (α ≫ β) • R = α • (β • R) := by
  cc_normalize

example (R : Resource A) : (𝟙 A • R : Resource A) = R := by
  cc_normalize

example {D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : Resource B) (S : Resource D) :
    (α ⊗ₘ β) • (R ∥ S) = (α • R) ∥ (β • S) := by
  cc_normalize

example {D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : Resource B) (S : Resource D) :
    ((α ⊗ₘ β) • (R ∥ S) : Resource (tensor A C)) = (α • R) ∥ (β • S) := by
  cc_normalize

example {D E : Interface} (γ : E ⟶ tensor A C) (α : A ⟶ B) (β : C ⟶ D)
    (R : Resource B) (S : Resource D) :
    (γ ≫ (α ⊗ₘ β)) • (R ∥ S) = γ • ((α • R) ∥ (β • S)) := by
  cc_normalize

example (α : A ⟶ B) (R S : Resource B) : Δ (α • R) (α • S) ≤ Δ R S := by
  cc_nonexpand

example (R S T : Resource A) : Δ R S ≤ Δ R T + Δ T S := by
  cc_triangle via T
  · exact le_rfl
  · exact le_rfl

example (α : A ⟶ B) (β : A ⟶ B) (R S : Resource B) :
    Δ (α • R) (β • S) ≤ Δ R S + Δ (α • S) (β • S) := by
  cc_triangle via (α • S)
  · cc_nonexpand
  · exact le_rfl

example (R S : Resource A) (T : Resource B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S := by
  cc_nonexpand

example (R : Resource A) (S T : Resource B) : Δ (R ∥ S) (R ∥ T) ≤ Δ S T := by
  cc_nonexpand

example (R S : Resource A) (T U : Resource B) :
    Δ (R ∥ T) (S ∥ U) ≤ Δ R S + Δ T U := by
  cc_nonexpand

example (R S : Resource A) (h : Δ R S ≤ 0) : Δ R S ≤ 0 := by
  fail_if_success cc_nonexpand
  exact h

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (R S : Resource A) (T : Resource B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S := by
  cc_nonexpand

example (α : A ⟶ B) (R : Resource B) :
    ({R} —[α]→ {α • R}) := by
  cc_construct using rfl

end SystemAlgebra.Usability
