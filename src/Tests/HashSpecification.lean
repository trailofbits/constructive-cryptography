module

public import Commons.Definitions.Hash.Specification

/-!
# Two implementations of a collision interface

On Boolean messages, the identity and complement hashes both report a collision exactly on
equal messages. A single construction transports both certificates through the same adapter.
-/

@[expose] public section

namespace HashSpecificationTests

open Commons ConstructiveCryptography SystemAlgebra
open scoped SystemAlgebra

noncomputable section

/-- Any injection on Boolean messages makes the real collision experiment the ideal one.
The experiment allows two queries, so an observer can request the key and submit a pair. -/
lemma real_eq_ideal_of_injective {T : Type} [DecidableEq T] (H : Unit → Bool → T)
    (injective : ∀ k, Function.Injective (H k)) :
    (Hash.Real H : TypedSystem (KeyedCollision Unit Bool 2)) = Hash.Ideal Unit Bool := by
  -- Injectivity identifies the Boolean replies of the collision branch.
  have collide (k : Unit) (m m' : Bool) :
      decide (H k m = H k m') = decide (m = m') := by
    simp only [(injective k).eq_iff]
  -- The key branch is shared, and both programs retain the same key after the first query.
  have body : Hash.Real.body H = Hash.Ideal.body Unit Bool := by
    funext stored i query
    cases i with
    | key => rfl
    | collide =>
      obtain ⟨m, m'⟩ := query
      cases stored <;> simp only [Hash.Real.body, Hash.Ideal.body, collide]
  simp only [Hash.Real, Hash.Ideal, Hash.Real.program, Hash.Ideal.program, body]
  rfl

local instance : AdmissibleDistinguishers Interface TypedDistinguisher := .all

/-- Any certified adapter on the collision interface gives zero distinguishing advantage
for both `m ↦ m` and `m ↦ !m`, including against the full observer class. -/
example {A : Interface} (α : TypedConverter A (KeyedCollision Unit Bool 2)) :
    (α • Hash.Real (budget := 2) (fun (_ : Unit) (m : Bool) => m) ≃[fun _ => 0]
      α • Hash.Ideal Unit Bool (budget := 2)) ∧
    (α • Hash.Real (budget := 2) (fun (_ : Unit) (m : Bool) => !m) ≃[fun _ => 0]
      α • Hash.Ideal Unit Bool (budget := 2)) := by
  -- Absorbing the adapter stays within the full observer class.
  have construction := Hash.CR.constructs_attach α (fun _ _ => Set.mem_univ _) (fun _ => 0)
  -- Each implementation discharges the same input specification using its own equality test.
  have applyConstruction (H : Unit → Bool → Bool) (injective : ∀ k, Function.Injective (H k)) :
      α • Hash.Real H (budget := 2) ≃[fun _ => 0] α • Hash.Ideal Unit Bool (budget := 2) := by
    apply construction
    rw [real_eq_ideal_of_injective H injective, Hash.CR.specification]
    exact Relaxation.subset_apply _ _ (Set.mem_singleton _)
  exact ⟨applyConstruction _ (fun _ => Function.injective_id),
    applyConstruction _ (fun _ a b h => by simpa only [Bool.not_not] using congrArg Bool.not h)⟩

end

end HashSpecificationTests
