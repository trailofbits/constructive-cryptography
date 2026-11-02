module

public import RandomSystems.Typed.ParallelAllContext
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Substitution.Reduction
public import Tests.FiniteFamilyCollect

/-!
# Component isolation in a common assembly

A bound on one changed component survives the existing family converters and an arbitrary
outside context. The same exact isolation equation also transports a selected-class contract
when the caller supplies its reduction, admissibility and advantage equation.
The Boolean/ternary source family is restored by plugging its original component back in.
Domain tests cover the inactive unit ports and both sides of the active query limit.
-/

@[expose] public section

namespace SystemAlgebra.Tests

open ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra NNReal

/-- Only the changed component's distance remains after placing it in the common assembly. -/
example
    -- `K` indexes the component interfaces `B j`; `α j` exposes `A j` to the outside context.
    {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface} {C : Interface}
    (context : TypedConverter C (⨂ j, A j)) (α : ∀ j, TypedConverter (A j) (B j))
    -- `R` fixes every other component, while `S`, `T` are the two systems at component `k`.
    (R : ∀ j, TypedSystem (B j)) (k : K) (S T : TypedSystem (B k))
    -- `hlocal` bounds the original component pair, before any context is attached.
    (ε : ℝ≥0) (hlocal : Δ S T ≤ ε) :
    Δ (context • ((⨂ₘ j, α j) • (∥ j, Function.update R k S j)))
      (context • ((⨂ₘ j, α j) • (∥ j, Function.update R k T j))) ≤ ε := by
  rw [← TypedConverter.parallelAllContext_smul R k S,
    ← TypedConverter.parallelAllContext_smul R k T]
  -- Each of the three existing attachments preserves the supplied component bound.
  exact (Interface.distance_smul_le context _ _).trans
    ((Interface.distance_smul_le (⨂ₘ j, α j) _ _).trans
      ((Interface.distance_smul_le (TypedConverter.parallelAllContext R k) S T).trans hlocal))

/-- A selected observation model requires its actual reduction and closure proof. -/
example
    -- `A j` is component `j`'s interface; `D B` carries the chosen tests on interface `B`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface} {D : Interface → Type}
    -- `model` selects these tests' advantages and admissibility.
    (model : DistinguisherAdvantage Interface TypedSystem D)
    -- `R j` fixes the other components; `k` selects the local pair `S`, `T`.
    (R : ∀ j, TypedSystem (A j)) (k : K) (S T : TypedSystem (A k))
    -- `reduce` absorbs the explicit isolation context; `closed` admits its transformed tests.
    (reduce : D (⨂ j, A j) → D (A k))
    (closed : ∀ d, d ∈ model.admissible (⨂ j, A j) → reduce d ∈ model.admissible (A k))
    -- `heq` connects the chosen advantage to this reduction.
    (heq : ∀ d (S T : TypedSystem (A k)), model.advantage (⨂ j, A j) d
      (TypedConverter.parallelAllContext R k • S) (TypedConverter.parallelAllContext R k • T) =
      model.advantage (A k) (reduce d) S T)
    -- `error` bounds local test advantage; `hlocal` is the component contract.
    (error : D (A k) → ENNReal) (hlocal : model.SubstitutesWithin error S T) :
    model.SubstitutesWithin (fun d => error (reduce d))
      (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) := by
  rw [← TypedConverter.parallelAllContext_smul R k S,
    ← TypedConverter.parallelAllContext_smul R k T]
  exact DistinguisherAdvantage.SubstitutesWithin.attach model
    (TypedConverter.parallelAllContext R k) reduce closed heq hlocal

/-- Restoring the Boolean source restores the original independent Boolean/ternary family. -/
example :
    TypedConverter.parallelAllContext (fun j => TypedSystem.source (collectionLaw j) 2) false •
      TypedSystem.source (collectionLaw false) 2 =
      ∥ j, TypedSystem.source (collectionLaw j) 2 := by
  rw [TypedConverter.parallelAllContext_smul, Function.update_eq_self]

/-- The inactive component has no ports. -/
example (i : (Interface.singleFamily (Interface.source Bool 2) false true).I) : False :=
  Empty.elim i

/-- The single-active-family domain still rejects the empty query history. -/
example : ¬ (⨂ j : Bool, Interface.singleFamily (Interface.source Bool 2) false j).domain [] := by
  change ¬ (⨂ j : Bool, Interface.singleFamily (Interface.source Bool 2) false j).domain
    ([].map (Interface.singleFamilyAlphabet (Interface.source Bool 2) false Interface.X).symm)
  rw [Interface.singleFamily_domain]
  exact (Interface.source Bool 2).nonempty_prefix.1

/-- The active component admits one embedded trigger within its one-query budget. -/
example : (⨂ j : Bool, Interface.singleFamily (Interface.source Bool 1) false j).domain
    ([⟨(), ()⟩].map
      (Interface.singleFamilyAlphabet (Interface.source Bool 1) false Interface.X).symm) := by
  rw [Interface.singleFamily_domain]
  exact ⟨by simp only [ne_eq, List.cons_ne_self, not_false_eq_true], le_refl _⟩

/-- Embedding two triggers cannot exceed the active component's one-query budget. -/
example : ¬ (⨂ j : Bool, Interface.singleFamily (Interface.source Bool 1) false j).domain
    ([⟨(), ()⟩, ⟨(), ()⟩].map
      (Interface.singleFamilyAlphabet (Interface.source Bool 1) false Interface.X).symm) := by
  rw [Interface.singleFamily_domain]
  intro h
  have hb := h.2
  norm_num only [List.length_cons, List.length_nil] at hb

#print axioms TypedConverter.singleFamily_smul
#print axioms TypedConverter.parallelAllContext_smul

end SystemAlgebra.Tests
