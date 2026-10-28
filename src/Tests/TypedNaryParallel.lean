import RandomSystems.Typed.ParallelAll

/-!
# Typed finite parallel families

The two components have different input and output alphabets. Fixed component functions
assemble into one function on the tagged interface. The parallel family's domain bound is
the sum of the two component bounds.
-/

namespace SystemAlgebra.Tests

open SystemAlgebra
open scoped SystemAlgebra

noncomputable section

def heterogeneousFamily : Bool → Interface
  | false => Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2
  | true => Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 1

example : (⨂ k, heterogeneousFamily k).bound = 3 := by
  simp [heterogeneousFamily]

example (f : ∀ k i, (heterogeneousFamily k).X i → (heterogeneousFamily k).Y i) :
    TypedSystem.ofFunction (A := ⨂ k, heterogeneousFamily k)
      (fun l x => f l.1 l.2 x) =
      ∥ k, TypedSystem.ofFunction (f k) :=
  TypedSystem.ofFunction_parallelAll f

abbrev bitInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

def fixedBit (c : Bool) : TypedSystem bitInterface :=
  TypedSystem.ofFunction fun _ _ => c

def sharedBit : TypedSystem (⨂ _k : Bool, bitInterface) :=
  TypedSystem.sample (Probability.Distribution.uniform Bool)
    (fun c => ∥ _k : Bool, fixedBit c)

def independentBit : TypedSystem (⨂ _k : Bool, bitInterface) :=
  ∥ _k : Bool, TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit

def mixedReplies : List
    ((Σ l, (⨂ _k : Bool, bitInterface).X l) ×
      (Σ l, (⨂ _k : Bool, bitInterface).Y l)) :=
  [(⟨⟨false, ()⟩, ()⟩, ⟨⟨false, ()⟩, false⟩),
    (⟨⟨true, ()⟩, ()⟩, ⟨⟨true, ()⟩, true⟩)]

/-- One shared bit cannot produce conflicting replies at the two components. -/
lemma sharedBit_mixedReplies_eq_zero : sharedBit.1 mixedReplies = 0 := by
  rw [sharedBit, TypedSystem.sample_mass]
  apply Finset.sum_eq_zero
  intro c hc
  have he : (∥ _k : Bool, fixedBit c) =
      TypedSystem.ofFunction (A := ⨂ _k : Bool, bitInterface) (fun _ _ => c) := by
    simpa [fixedBit] using (TypedSystem.ofFunction_parallelAll
      (A := fun _k : Bool => bitInterface) (fun _k _ _ => c)).symm
  rw [he, TypedSystem.ofFunction_mass]
  simp [mixedReplies]

/-- Independent component samples can produce those mixed replies. -/
lemma independentBit_mixedReplies_eq_quarter :
    independentBit.1 mixedReplies = (1 / 4 : ℝ) := by
  rw [independentBit, TypedSystem.parallelAll_mass, RandomSystem.parallelAll_mass]
  simp [Equiv.sigmaAssoc, RandomSystem.parallelAllConsistent, RandomSystem.restrictExchanges,
    TypedSystem.sample_mass, TypedSystem.ofFunction_mass, fixedBit, bitInterface,
    mixedReplies, Probability.Distribution.uniform_apply]
  norm_num

/-- Sampling one shared table differs from sampling each component independently. -/
example : sharedBit ≠ independentBit := by
  intro he
  have hm := congrArg (fun R : TypedSystem (⨂ _k : Bool, bitInterface) => R.1 mixedReplies) he
  rw [sharedBit_mixedReplies_eq_zero, independentBit_mixedReplies_eq_quarter] at hm
  norm_num at hm

#print axioms SystemAlgebra.TypedSystem.parallelAll
#print axioms SystemAlgebra.TypedSystem.ofFunction_parallelAll
#print axioms SystemAlgebra.TypedConverter.parallelAll

end
end SystemAlgebra.Tests
