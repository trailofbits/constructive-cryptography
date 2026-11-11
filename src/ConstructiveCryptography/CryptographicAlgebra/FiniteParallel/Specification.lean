module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel

/-!
# Properties of a selected component

`mem_parallelAll_of_mem` transports an indexed specification from one component to its whole
family. An equivalence selects the component as the head; three supplied `Constructs`
contracts preserve its property when adjoining the tail, undoing the split, and reindexing.

```text
selected head ── parallel with tail ──▶ split family ── split.hom ──▶ reindexed family
                                                                         │ reindex.hom
                                                                         ▼
                                                                   original family
```

The property indices record data such as an observed part of a reply. Each contract states
how that data changes at its own presentation. The remaining components are arbitrary.
-/

public section

namespace ConstructiveCryptography.FiniteParallel

open CategoryTheory MonoidalCategory CryptographicAlgebra
open ConstructiveCryptography.Specification (Constructs)
open scoped ConstructiveCryptography.FiniteParallel

universe u v w x

-- `C` carries interfaces and converters; `Phi A` carries resources at interface `A : C`.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CryptographicAlgebra C Phi]
variable [FiniteParallel C Phi]

/-- A property of the selected component extends to the family through its three contracts. -/
theorem mem_parallelAll_of_mem
    -- `Index A` carries property parameters at `A`; `P A i` is their resource specification.
    {Index : C → Type x} (P : ∀ A, Index A → Specification (Phi A))
    -- `e none` selects the head in the original index type `K`; `J` indexes the remaining tail.
    {K J : Type} [Fintype K] [Fintype J] (e : Option J ≃ K)
    -- `A k` is component `k`'s interface and `R k` its resource.
    {A : K → C} (R : ∀ k, Phi (A k))
    -- `leftIndex` extends the head's property parameters to the head beside its tail.
    (leftIndex : Index (A (e none)) →
      Index (A (e none) ⊗ (⨂ j, A (e (some j)))))
    -- `splitIndex` reads those parameters on the equivalent `Option J` family interface.
    (splitIndex : Index (A (e none) ⊗ (⨂ j, A (e (some j)))) →
      Index (⨂ o, A (e o)))
    -- `reindexIndex` returns the parameters to the original `K` family interface.
    (reindexIndex : Index (⨂ o, A (e o)) → Index (⨂ k, A k))
    -- `left` preserves the indexed property when the actual remaining resources are adjoined.
    (left : ∀ i, Constructs (fun S => parallel S (∥ j, R (e (some j))))
      (P _ i) (P _ (leftIndex i)))
    -- `split` transports it through the chosen head/tail presentation.
    (split : ∀ i, Constructs (attach (optionSplit (fun o => A (e o))).hom)
      (P _ i) (P _ (splitIndex i)))
    -- `reindexed` transports it through this particular reindexing presentation.
    (reindexed : ∀ i, Constructs (attach (reindex e A).hom)
      (P _ i) (P _ (reindexIndex i)))
    -- `selected` is the sole component premise; the conclusion records all three index maps.
    {i : Index (A (e none))} (selected : R (e none) ∈ P _ i) :
    (∥ k, R k) ∈ P _ (reindexIndex (splitIndex (leftIndex i))) := by
  -- Compose the three specification maps on the selected component's guarantee.
  have transported := ((reindexed _).comp ((split _).comp (left i))) selected
  -- Identify their resulting assembly with the original family by the presentation laws.
  change (reindex e A).hom • ((optionSplit (fun o => A (e o))).hom •
    parallel (R (e none)) (∥ j, R (e (some j)))) ∈ _ at transported
  rw [optionSplit_parallelAll (fun o => A (e o)) (fun o => R (e o)),
    reindex_parallelAll e A R] at transported
  exact transported

end ConstructiveCryptography.FiniteParallel
