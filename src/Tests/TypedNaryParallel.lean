import RandomSystems.Typed.ParallelAttachment
import RandomSystems.Typed.ParallelAllAttachment
import RandomSystems.Typed.ParallelAllRegroup

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

/-- Independent presentations assemble even when the two components use different alphabets. -/
example (P : ∀ k : Bool, Probability.Distribution.ProbDist
    {s : InterfaceSystem (heterogeneousFamily k).I (heterogeneousFamily k).X
      (heterogeneousFamily k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧
        ∀ h, (s h).Dom ↔ (heterogeneousFamily k).domain h}) :
    (∥ k, TypedSystem.ofPDS (P k)) =
      TypedSystem.ofPDS (TypedSystem.parallelAllPDS P) :=
  TypedSystem.parallelAll_ofPDS P

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

/-- Locality elaborates directly for heterogeneous stochastic components. -/
example (α : ∀ k, TypedConverter (heterogeneousFamily k) (heterogeneousFamily k))
    (R : ∀ k, TypedSystem (heterogeneousFamily k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) :=
  TypedConverter.parallelAll_attach α R

/-- The same statement admits the empty family without a positive budget assumption. -/
example {A B : Empty → Interface} (α : ∀ k, TypedConverter (A k) (B k))
    (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) :=
  TypedConverter.parallelAll_attach α R

/-- A component budget of one permits two total queries; a shared total budget of one does not. -/
example :
    (⨂ _k : Bool, bitInterface).domain
      [⟨⟨false, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩] ∧
    ¬ (Interface.queryBudget (Σ _k : Bool, Unit) (fun _ => Unit) (fun _ => Bool) 1).domain
      [⟨⟨false, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩] := by
  simp [Interface.tensorAll, parallelAllInputs, bitInterface,
    Interface.queryBudget, Equiv.sigmaAssoc, SystemAlgebra.restrict]

/-- The binary bridge retains both the family tag and the component's local port. -/
example {A : Option Unit → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (⨂ k, A k).X l) × (Σ l, (⨂ k, A k).Y l))) :
    (∥ k, R k).1 h = (TypedSystem.parallel (R none) (R (some ()))).1
      (h.map ((Interface.optionFamilyAlphabet fun k => (A k).X).prodCongr
        (Interface.optionFamilyAlphabet fun k => (A k).Y))) :=
  TypedSystem.parallelAll_option_mass R h

/-- **Two components in family and binary form**: for arbitrary stochastic systems and
converters, family attachment and binary attachment have equal cumulative probabilities
after `optionFamilyAlphabet` maps the family-tagged transcript to the binary interface. -/
example {A B : Option Unit → Interface} (α : ∀ k, TypedConverter (A k) (B k))
    (R : ∀ k, TypedSystem (B k))
    (h : List ((Σ l, (⨂ k, A k).X l) × (Σ l, (⨂ k, A k).Y l))) :
    ((⨂ₘ k, α k) • (∥ k, R k)).1 h =
      (TypedConverter.parallel (α none) (α (some ())) •
        TypedSystem.parallel (R none) (R (some ()))).1
        (h.map ((Interface.optionFamilyAlphabet fun k => (A k).X).prodCongr
          (Interface.optionFamilyAlphabet fun k => (A k).Y))) := by
  -- Locality attaches each converter to its own component on both sides.
  rw [TypedConverter.parallelAll_attach, TypedConverter.parallel_attach]
  -- The remaining parallel systems agree after relabelling the transcript's interface tags.
  exact TypedSystem.parallelAll_option_mass _ h

#print axioms SystemAlgebra.parAll_interconnect_all
#print axioms SystemAlgebra.trim_apply_tensorAllL_parAll
#print axioms SystemAlgebra.TypedConverter.parallelAll_attach
#print axioms SystemAlgebra.TypedConverter.parallelAll_attach_ofFunction
#print axioms SystemAlgebra.TypedSystem.parallelAll_option_mass

#print axioms SystemAlgebra.TypedSystem.parallelAll
#print axioms SystemAlgebra.TypedSystem.ofFunction_parallelAll
#print axioms SystemAlgebra.TypedConverter.parallelAll
#print axioms SystemAlgebra.TypedSystem.parallelAll_ofPDS

end
end SystemAlgebra.Tests
