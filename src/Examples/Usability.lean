import ConstructiveCryptography.Notation
import Commons.Definitions.Ideal

/-!
# Proof commands on interfaces

The CC notation and proof commands on arbitrary interfaces: normalization of attachment and
parallel composition (`cc_normalize`), non-expansion (`cc_nonexpand`), the triangle
inequality (`cc_triangle`), and exact construction (`cc_construct`).
The first example compares two systems built from `Commons.StrongURP`, whose forward and
inverse ports share one retained permutation. Their equality lifts through a common context.
-/

namespace SystemAlgebra.Usability

open CategoryTheory CategoryTheory.MonoidalCategory
open Interface
open scoped SystemAlgebra

variable {A B C : Interface}

/-- Both environments attach a converter to one `Commons.StrongURP X` beside `T` inside
`context`. `cc_normalize` brings both sides to the same wiring; the local equation `component`
then closes the comparison. -/
example
    -- `X` is the finite permuted set; `q` bounds the combined forward and inverse queries.
    {X : Type} [Fintype X] {q : ℕ}
    -- `first`, `second : A ⟶ Commons.Bidirectional X q` answer `A`-queries with forward and
    -- inverse queries to the one permutation.
    (first second : A ⟶ Commons.Bidirectional X q)
    -- `context` answers `C`-queries through the component's `A` and the unchanged system
    -- `T : TypedSystem B`.
    (context : C ⟶ A ⊗ B) (T : TypedSystem B)
    -- `component`: the two converters give equal systems on the same `StrongURP X`.
    (component : first • Commons.StrongURP X = second • Commons.StrongURP X) :
    context • ((first • Commons.StrongURP X) ∥ T) =
      (context ≫ (second ⊗ₘ 𝟙 B)) • (Commons.StrongURP X ∥ T) := by
  cc_normalize
  rw [component]

example (α : A ⟶ B) (β : B ⟶ C) (R : TypedSystem C) :
    (α ≫ β) • R = α • (β • R) := by
  cc_normalize

example (R : TypedSystem A) : (𝟙 A • R : TypedSystem A) = R := by
  cc_normalize

example {D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : TypedSystem B) (S : TypedSystem D) :
    (α ⊗ₘ β) • (R ∥ S) = (α • R) ∥ (β • S) := by
  cc_normalize

example {D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : TypedSystem B) (S : TypedSystem D) :
    ((α ⊗ₘ β) • (R ∥ S) : TypedSystem (tensor A C)) = (α • R) ∥ (β • S) := by
  cc_normalize

example {D E : Interface} (γ : E ⟶ tensor A C) (α : A ⟶ B) (β : C ⟶ D)
    (R : TypedSystem B) (S : TypedSystem D) :
    (γ ≫ (α ⊗ₘ β)) • (R ∥ S) = γ • ((α • R) ∥ (β • S)) := by
  cc_normalize

example (α : A ⟶ B) (R S : TypedSystem B) : Δ (α • R) (α • S) ≤ Δ R S := by
  cc_nonexpand

example (R S T : TypedSystem A) : Δ R S ≤ Δ R T + Δ T S := by
  cc_triangle via T
  · exact le_rfl
  · exact le_rfl

example (α : A ⟶ B) (β : A ⟶ B) (R S : TypedSystem B) :
    Δ (α • R) (β • S) ≤ Δ R S + Δ (α • S) (β • S) := by
  cc_triangle via (α • S)
  · cc_nonexpand
  · exact le_rfl

example (R S : TypedSystem A) (T : TypedSystem B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S := by
  cc_nonexpand

example (R : TypedSystem A) (S T : TypedSystem B) : Δ (R ∥ S) (R ∥ T) ≤ Δ S T := by
  cc_nonexpand

example (R S : TypedSystem A) (T U : TypedSystem B) :
    Δ (R ∥ T) (S ∥ U) ≤ Δ R S + Δ T U := by
  cc_nonexpand

example (R S : TypedSystem A) (h : Δ R S ≤ 0) : Δ R S ≤ 0 := by
  fail_if_success cc_nonexpand
  exact h

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (R S : TypedSystem A) (T : TypedSystem B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S := by
  cc_nonexpand

example (α : A ⟶ B) (R : TypedSystem B) :
    ({R} —[α]→ {α • R}) := by
  cc_construct using rfl

end SystemAlgebra.Usability
