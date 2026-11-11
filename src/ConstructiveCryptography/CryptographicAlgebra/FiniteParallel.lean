module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel.Defs

/-!
# Finite-family transport and attachment

`reindex_inv_parallelAll` and `optionSplit_inv_parallelAll` expose the inverse presentations
of a family. `optionSplit_attach_parallelAll` factors family attachment through the binary
head and tail presentation, using the existing binary attachment law. All equations concern
assembled resources, with the chosen converter action and explicit interface isomorphisms.
`context_split_attachment` carries the same factorization through a shared outside converter.
-/

public section

namespace ConstructiveCryptography

open CategoryTheory MonoidalCategory CryptographicAlgebra

universe u v w

-- `C` carries interfaces and converters; `Phi A` carries resources presenting `A`.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CryptographicAlgebra C Phi]
variable [FiniteParallel C Phi]

namespace FiniteParallel

open scoped ConstructiveCryptography.FiniteParallel

/-- Undoing a family reindexing recovers its reindexed components. -/
lemma reindex_inv_parallelAll {K L : Type} [Fintype K] [Fintype L]
    -- `e` presents the `K`-indexed interfaces `A` using indices in `L`.
    (e : L ≃ K) (A : K → C) (R : ∀ k, Phi (A k)) :
    (reindex e A).inv • (∥ k, R k) = (∥ l, R (e l)) :=
  ResourceTheory.attach_iso_inv_of_eq (reindex e A) _ _ (reindex_parallelAll e A R)

/-- Undoing the split presentation recovers the head beside its remaining family. -/
lemma optionSplit_inv_parallelAll {K : Type} [Fintype K]
    -- `A none` is the head interface; `A (some k)` are the tail interfaces.
    (A : Option K → C) (R : ∀ k, Phi (A k)) :
    (optionSplit A).inv • (∥ k, R k) =
      parallel (R none) (∥ k, R (some k)) :=
  ResourceTheory.attach_iso_inv_of_eq (optionSplit A) _ _ (optionSplit_parallelAll A R)

/-- Family attachment can be performed separately on the head and tail before assembly. -/
lemma optionSplit_attach_parallelAll {K : Type} [Fintype K]
    -- `α k` connects outside interface `A k` to the resource interface `B k`.
    {A B : Option K → C} (α : ∀ k, A k ⟶ B k) (R : ∀ k, Phi (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) =
      (optionSplit A).hom •
        ((α none ⊗ₘ (⨂ₘ k, α (some k))) •
          parallel (R none) (∥ k, R (some k))) := by
  calc
    (⨂ₘ k, α k) • (∥ k, R k) = (∥ k, α k • R k) :=
      attach_parallelAll α R
    _ = (optionSplit A).hom •
        parallel (α none • R none) (∥ k, α (some k) • R (some k)) :=
      (optionSplit_parallelAll A (fun k => α k • R k)).symm
    _ = _ := by
      apply congrArg (fun S => (optionSplit A).hom • S)
      rw [← attach_parallelAll (fun k => α (some k)) (fun k => R (some k))]
      exact (attach_parallel (α none) (⨂ₘ k, α (some k))
        (R none) (∥ k, R (some k))).symm

/-- Splitting the family and distributing local attachments preserves the fixed context. -/
lemma context_split_attachment {K : Type} [Fintype K] {A B : Option K → C} {X : C}
    -- `context` is the shared outside converter; `α k` acts on resource `R k` at `B k`.
    (context : X ⟶ ⨂ k, A k) (α : ∀ k, A k ⟶ B k) (R : ∀ k, Phi (B k)) :
    (context ≫ ⨂ₘ k, α k) • (∥ k, R k) =
      (context ≫ (optionSplit A).hom) •
        ((α none ⊗ₘ (⨂ₘ k, α (some k))) •
          parallel (R none) (∥ k, R (some k))) := by
  calc
    (context ≫ ⨂ₘ k, α k) • (∥ k, R k) =
        context • ((⨂ₘ k, α k) • (∥ k, R k)) := attach_serial _ _ _
    _ = context • ((optionSplit A).hom •
        ((α none ⊗ₘ (⨂ₘ k, α (some k))) •
          parallel (R none) (∥ k, R (some k)))) :=
      congrArg (fun S => context • S) (optionSplit_attach_parallelAll α R)
    _ = _ := (attach_serial _ _ _).symm

end FiniteParallel

end ConstructiveCryptography
