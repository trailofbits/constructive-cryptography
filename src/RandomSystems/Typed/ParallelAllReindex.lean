module

public import RandomSystems.Typed.ParallelAllReindex.Defs

/-!
# Coherent family reindexing

`TypedConverter.reindex_refl` and `TypedConverter.reindex_comp` derive identity and serial
coherence from the corresponding laws of renaming. `TypedConverter.reindex_parallelAll`
expresses their action on assembled resources, using the cumulative reindexing law.
-/

@[expose] public section

namespace SystemAlgebra

/-- Identity family reindexing leaves every local label unchanged. -/
lemma reindexLabels_refl {K : Type} (A : K → Interface) (F : ∀ k, (A k).I → Type) :
    reindexLabels (Equiv.refl K) A F = Equiv.refl _ := by
  apply Equiv.ext
  rintro ⟨⟨k, i⟩, x⟩
  rfl

/-- Composing family reindexings composes their label bijections in the same order. -/
lemma reindexLabels_trans {K L M : Type} (e : L ≃ K) (f : M ≃ L)
    (A : K → Interface) (F : ∀ k, (A k).I → Type) :
    reindexLabels (f.trans e) A F =
      (reindexLabels e A F).trans (reindexLabels f (fun l => A (e l)) (fun l => F (e l))) := by
  have h : ((reindexLabels e A F).trans
      (reindexLabels f (fun l => A (e l)) (fun l => F (e l)))).symm =
      (reindexLabels (f.trans e) A F).symm := by
    apply Equiv.ext
    rintro ⟨⟨m, i⟩, x⟩
    rfl
  exact (congrArg Equiv.symm h).symm

namespace TypedConverter

/-- The identity family equivalence induces the identity converter. -/
lemma reindex_refl {K : Type} [Fintype K] (A : K → Interface) :
    reindex (Equiv.refl K) A = TypedConverter.id (Interface.tensorAll A) := by
  have hp : (Equiv.sigmaCongrLeft (β := fun k => (A k).I) (Equiv.refl K)).symm =
      Equiv.refl _ := by
    apply Equiv.ext
    rintro ⟨k, i⟩
    rfl
  simp only [reindex, hp, reindexLabels_refl]
  exact rename_refl _

/-- Serial family reindexing is reindexing by the composite equivalence. -/
lemma reindex_comp {K L M : Type} [Fintype K] [Fintype L] [Fintype M]
    (e : L ≃ K) (f : M ≃ L) (A : K → Interface) :
    comp (reindex e A) (reindex f (fun l => A (e l))) = reindex (f.trans e) A := by
  have hp : (Equiv.sigmaCongrLeft (β := fun k => (A k).I) (f.trans e)).symm =
      (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm.trans
        (Equiv.sigmaCongrLeft (β := fun l => (A (e l)).I) f).symm := by
    have h : Equiv.sigmaCongrLeft (β := fun k => (A k).I) (f.trans e) =
        (Equiv.sigmaCongrLeft (β := fun l => (A (e l)).I) f).trans
          (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e) := by
      apply Equiv.ext
      rintro ⟨m, i⟩
      rfl
    exact congrArg Equiv.symm h
  simp only [reindex, rename_comp, hp, reindexLabels_trans]
  rfl

open Classical in
/-- Reindexing an assembled family preserves its component resources. -/
lemma reindex_parallelAll {K L : Type} [Fintype K] [Fintype L]
    (e : L ≃ K) {A : K → Interface} (R : ∀ k, TypedSystem (A k)) :
    reindex e A • TypedSystem.parallelAll (fun l => R (e l)) = TypedSystem.parallelAll R :=
  (TypedSystem.parallelAll_reindex e R).symm

end TypedConverter

end SystemAlgebra
