import RandomSystems.Typed.ParallelAll
import RandomSystems.Cumulative.ParallelAllRegroup

/-!
# Regrouping a typed pair as a finite family

For `A : Option Unit → Interface`, the n-ary interface `⨂ k, A k` has labels `⟨k, i⟩` and the
binary `tensor (A none) (A (some ()))` has labels `inl i`, `inr i`. These are different types;
the explicit alphabet equivalence `optionFamilyAlphabet` relates them, and on corresponding
transcripts

  `(∥ k, R k)(h) = (parallel (R none) (R (some ())))(h.map (φ_X × φ_Y))`.

No definitional identification of the two interfaces and no implicit unitor is used.

## Main definitions

* `Interface.optionFamilyAlphabet F`: `⟨⟨none, i⟩, x⟩ ↦ ⟨inl i, x⟩`,
  `⟨⟨some (), i⟩, x⟩ ↦ ⟨inr i, x⟩`

## Main results

* `TypedSystem.parallelAll_option_mass`: the n-ary product of two is the binary product
-/

namespace SystemAlgebra

open Interface

open Classical in
/-- The two family tags as the binary label sum, keeping every local port and value:

```text
  ⟨⟨none, i⟩, x⟩ ↦ ⟨none, ⟨i, x⟩⟩ ↦ ⟨none, ⟨i, x⟩⟩ ↦ ⟨inl i, x⟩
                sigmaAssoc      optionPair       sumAlphabet
```
-/
def Interface.optionFamilyAlphabet {I : Option Unit → Type} (F : ∀ k, I k → Type) :
    (Σ l : Σ k, I k, F l.1 l.2) ≃
      Σ l, Sum.rec (F none) (F (some ())) l :=
  (Equiv.sigmaAssoc F).trans ((optionPair (fun k => Σ i, F k i)).trans
    (sumAlphabet (Sum.rec (F none) (F (some ())))))

open Classical in
/-- **The typed n-ary product of two components is the binary product**: with
`φ = optionFamilyAlphabet`,

  `(∥ k, R k)(h) = (parallel (R none) (R (some ())))(h.map (φ_X × φ_Y))`. -/
lemma TypedSystem.parallelAll_option_mass {A : Option Unit → Interface}
    (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (tensorAll A).X l) × (Σ l, (tensorAll A).Y l))) :
    (TypedSystem.parallelAll R).1 h =
      (TypedSystem.parallel (R none) (R (some ()))).1
        (h.map ((optionFamilyAlphabet fun k => (A k).X).prodCongr
          (optionFamilyAlphabet fun k => (A k).Y))) := by
  -- Unfold both typed products to cumulative ones and apply the cumulative bridge. The left
  -- reads `h` through `optionPair ∘ sigmaAssoc`, the right through `sumAlphabet⁻¹ ∘ φ`.
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_option_mass,
    TypedSystem.parallel_mass]
  apply congrArg (fun t => RandomSystem.parallel (R none).1 (R (some ())).1 t)
  simp only [List.map_map]
  apply List.map_congr_left
  intro z _
  -- On each exchange `sumAlphabet⁻¹ ∘ φ = optionPair ∘ sigmaAssoc`, since `φ` ends in
  -- `sumAlphabet`.
  apply Prod.ext <;>
    simp only [Equiv.prodCongr_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd,
      optionFamilyAlphabet, Equiv.coe_trans, Equiv.symm_apply_apply]

end SystemAlgebra
