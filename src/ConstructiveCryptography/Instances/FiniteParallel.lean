module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel
public import ConstructiveCryptography.Instances.Algebra
public import RandomSystems.Typed.ParallelAllAttachment
public import RandomSystems.Typed.ParallelAllReindex

/-!
# Finite parallel families of interfaces

`Interface.finiteParallel` selects `Interface.tensorAll`, `TypedConverter.parallelAll` and
`TypedSystem.parallelAll`. Its reindexing, head/tail and empty-unit isomorphisms package the
existing domain-preserving alphabet equivalences with `Interface.isoOf`.

Family attachment is `TypedConverter.parallelAll_attach`; resource presentation equations
are the typed regrouping laws. Reindexing identity and composition use
`TypedConverter.reindex_refl` and `TypedConverter.reindex_comp`. Thus the abstract family
calculus applies to the existing independent products and their declared domains.
-/

@[expose] public section

namespace SystemAlgebra.Interface

open Classical in
/-- The chosen finite-family operations on interfaces and typed systems, with explicit rewiring. -/
noncomputable instance finiteParallel :
    ConstructiveCryptography.FiniteParallel Interface TypedSystem where
  tensorAll := Interface.tensorAll
  tensorAllHom := TypedConverter.parallelAll
  parallelAll := TypedSystem.parallelAll
  reindex e A := isoOf
    (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm
    (reindexLabels e A fun k i => (A k).X i) (reindexLabels e A fun k i => (A k).Y i)
    (reindexLabels_fst e A fun k i => (A k).X i)
    (reindexLabels_fst e A fun k i => (A k).Y i) (tensorAll_domain_reindexLabels e A)
  optionSplit A := isoOf (optionSplitPorts A)
    (optionSplitLabels A fun o i => (A o).X i) (optionSplitLabels A fun o i => (A o).Y i)
    (optionSplitLabels_fst A fun o i => (A o).X i)
    (optionSplitLabels_fst A fun o i => (A o).Y i) (tensor_domain_optionSplitLabels A)
  empty A := isoOf (A := Interface.tensorAll A) (B := Interface.unit)
    (Equiv.equivEmpty _) (Equiv.equivOfIsEmpty _ _) (Equiv.equivOfIsEmpty _ _)
    (fun x => x.1.1.elim) (fun y => y.1.1.elim)
    (fun h => iff_of_false id (tensorAll_domain_empty A h))
  attach_parallelAll := TypedConverter.parallelAll_attach
  reindex_refl := TypedConverter.reindex_refl
  reindex_trans e f A := (TypedConverter.reindex_comp e f A).symm
  reindex_parallelAll e A R := TypedConverter.reindex_parallelAll e R
  optionSplit_parallelAll {K} _ A R := by
    -- The split law uses Option's derived equality decision; the selected family uses classical.
    have h := (TypedSystem.parallelAll_optionSplit A R).symm
    have hd : (@Option.instDecidableEq K (Classical.decEq K)) = Classical.decEq (Option K) :=
      Subsingleton.elim _ _
    rw [hd] at h
    exact h
  empty_parallelAll A R := (TypedSystem.parallelAll_empty A R).symm

/-- The abstract family operation is the typed product for any caller's index equality decision. -/
lemma cc_parallelAll_eq {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    (R : ∀ k, TypedSystem (A k)) :
    ConstructiveCryptography.FiniteParallel.parallelAll R = TypedSystem.parallelAll R := by
  change @TypedSystem.parallelAll K _ (Classical.decEq K) A R = TypedSystem.parallelAll R
  rw [Subsingleton.elim (Classical.decEq K) (inferInstance : DecidableEq K)]

end SystemAlgebra.Interface
