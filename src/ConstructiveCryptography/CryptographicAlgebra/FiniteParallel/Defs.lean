module

public import ConstructiveCryptography.CryptographicAlgebra.Basic
public import Mathlib.Data.Fintype.Option

/-!
# Chosen finite parallel families

`FiniteParallel` adds finite interface, converter and resource families to a cryptographic
algebra. Explicit isomorphisms identify reindexing, an `Option` head and tail, and the empty
family with their ordered presentations. Its attachment law acts componentwise.

The contract selects finite presentations of the existing binary algebra.

```text
family R ── split.inv ── R none ∥ family (R ∘ some)
family R ── family α  ── family (fun k => α k • R k)
```

The inverse transport and assembly laws live in
`ConstructiveCryptography.CryptographicAlgebra.FiniteParallel`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open ConstructiveCryptography CryptographicAlgebra

universe u v w

namespace ConstructiveCryptography

/-- Chosen finite families compatible with attachment and ordered binary parallel. -/
class FiniteParallel
    -- `C` carries interfaces and converters; its tensor is ordered parallel.
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    -- `Phi A` carries resources at interface `A`; attachment is contravariant.
    (Phi : outParam (C → Type w)) [ResourceTheory C Phi] [CryptographicAlgebra C Phi] where
  /-- The interface of a finite family `A`, where `A k` is its `k`th interface. -/
  tensorAll : ∀ {K : Type} [Fintype K], (K → C) → C
  /-- Place converters with matching family indices side by side. -/
  tensorAllHom : ∀ {K : Type} [Fintype K] {A B : K → C},
    (∀ k, A k ⟶ B k) → (tensorAll A ⟶ tensorAll B)
  /-- Assemble resources at the chosen family interface. -/
  parallelAll : ∀ {K : Type} [Fintype K] {A : K → C},
    (∀ k, Phi (A k)) → Phi (tensorAll A)
  /-- Present a family indexed by `K` through an equivalence `e : L ≃ K`. -/
  reindex : ∀ {K L : Type} [Fintype K] [Fintype L] (e : L ≃ K) (A : K → C),
    tensorAll A ≅ tensorAll (fun l => A (e l))
  /-- Separate the `none` component from the `some` components in that order. -/
  optionSplit : ∀ {K : Type} [Fintype K] (A : Option K → C),
    tensorAll A ≅ A none ⊗ tensorAll (fun k => A (some k))
  /-- Identify the empty family interface with the monoidal unit. -/
  empty : ∀ (A : PEmpty → C), tensorAll A ≅ 𝟙_ C
  /-- A family of converters acts componentwise on the matching resources. -/
  attach_parallelAll : ∀ {K : Type} [Fintype K] {A B : K → C}
    (α : ∀ k, A k ⟶ B k) (R : ∀ k, Phi (B k)),
    tensorAllHom α • parallelAll R = parallelAll (fun k => α k • R k)
  /-- Reindexing by the identity equivalence is the identity converter. -/
  reindex_refl : ∀ {K : Type} [Fintype K] (A : K → C),
    (reindex (Equiv.refl K) A).hom = 𝟙 (tensorAll A)
  /-- Successive reindexings compose in converter order. -/
  reindex_trans : ∀ {K L M : Type} [Fintype K] [Fintype L] [Fintype M]
    (e : L ≃ K) (f : M ≃ L) (A : K → C),
    (reindex (f.trans e) A).hom = (reindex e A).hom ≫
      (reindex f (fun l => A (e l))).hom
  /-- Reindexing preserves the assembled resource. -/
  reindex_parallelAll : ∀ {K L : Type} [Fintype K] [Fintype L]
    (e : L ≃ K) (A : K → C) (R : ∀ k, Phi (A k)),
    (reindex e A).hom • parallelAll (fun l => R (e l)) = parallelAll R
  /-- The head and tail presentation assembles the original resource family. -/
  optionSplit_parallelAll : ∀ {K : Type} [Fintype K]
    (A : Option K → C) (R : ∀ k, Phi (A k)),
    (optionSplit A).hom • parallel (R none) (parallelAll (fun k => R (some k))) =
      parallelAll R
  /-- The empty resource family is the dummy resource through its unit isomorphism. -/
  empty_parallelAll : ∀ (A : PEmpty → C) (R : ∀ k, Phi (A k)),
    (empty A).hom • (dummy (C := C) (Phi := Phi)) = parallelAll R

namespace FiniteParallel

-- When both family scopes are open, these binders select the abstract chosen operations.
/-- Finite family interfaces in the abstract algebra. -/
scoped notation3 (priority := high) "⨂ "(...)", "r:(scoped A => tensorAll A) => r

/-- Finite resource families in the abstract algebra. -/
scoped notation3 (priority := high) "∥ "(...)", "r:(scoped R => parallelAll R) => r

/-- Finite converter families in the abstract algebra. -/
scoped notation3 (priority := high) "⨂ₘ "(...)", "r:(scoped α => tensorAllHom α) => r

end FiniteParallel

end ConstructiveCryptography
