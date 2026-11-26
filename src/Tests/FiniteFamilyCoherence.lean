module

public import RandomSystems.Typed.ParallelAllReindex
public import Tests.TypedNaryParallel

/-!
# Concrete finite-family presentations

The empty family is an explicitly renamed dummy. A singleton splits into its bit component
and the empty tail. Reindexing the existing heterogeneous Boolean/unit family preserves its
component systems, and the categorical isomorphism uses the same forwarding converter.
-/

public section

namespace SystemAlgebra.Tests

open scoped SystemAlgebra

/-- The empty family of bit resources is a renamed dummy. -/
example : ∃ α : TypedConverter (⨂ _ : PEmpty, bitInterface) Interface.unit,
    (∥ _ : PEmpty, fixedBit false) = α • TypedSystem.dummy :=
  ⟨_, TypedSystem.parallelAll_empty (fun _ => bitInterface) (fun _ => fixedBit false)⟩

/-- A singleton bit resource splits from its empty tail by the declared alphabet wiring. -/
example : ∃ α : TypedConverter (⨂ _ : Option PEmpty, bitInterface)
      (Interface.tensor bitInterface (⨂ _ : PEmpty, bitInterface)),
    (∥ _ : Option PEmpty, fixedBit false) =
      α • TypedSystem.parallel (fixedBit false) (∥ _ : PEmpty, fixedBit false) :=
  ⟨_, TypedSystem.parallelAll_optionSplit (fun _ => bitInterface) (fun _ => fixedBit false)⟩

/-- Each heterogeneous component returns its input at its own Boolean or unit alphabet. -/
noncomputable def heterogeneousIdentity : ∀ k, TypedSystem (heterogeneousFamily k)
  | false => TypedSystem.ofFunction (fun _ x => x)
  | true => TypedSystem.ofFunction (fun _ x => x)

-- Match the chosen classical index equality used by the general regrouping contract.
noncomputable local instance : DecidableEq Bool := Classical.decEq Bool

/-- Swapping components with different alphabets and budgets preserves their identity replies. -/
example : TypedConverter.reindex (Equiv.swap false true) heterogeneousFamily •
      (∥ k, heterogeneousIdentity (Equiv.swap false true k)) =
      ∥ k, heterogeneousIdentity k :=
  TypedConverter.reindex_parallelAll (Equiv.swap false true) heterogeneousIdentity

/-- The abstract interface isomorphism packages the existing systems-level converter exactly. -/
example {K L : Type} [Fintype K] [Fintype L] (e : L ≃ K) (A : K → Interface) :
    (Interface.isoOf (A := Interface.tensorAll A) (B := Interface.tensorAll fun l => A (e l))
      (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm
      (reindexLabels e A fun k i => (A k).X i) (reindexLabels e A fun k i => (A k).Y i)
      (reindexLabels_fst e A fun k i => (A k).X i)
      (reindexLabels_fst e A fun k i => (A k).Y i) (tensorAll_domain_reindexLabels e A)).hom =
      TypedConverter.reindex e A := rfl

#print axioms TypedSystem.parallelAll_empty
#print axioms TypedSystem.parallelAll_optionSplit
#print axioms TypedConverter.reindex_refl
#print axioms TypedConverter.reindex_comp

end SystemAlgebra.Tests
