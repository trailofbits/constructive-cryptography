module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Logic.Function.Basic

/-!
# Encoding a finite subset

`Set.Finite.exists_fin_encoding` represents a finite subset `K` of an arbitrary type `X`
using `Fin n`. The encoder is defined on all of `X`, and the injective decoder satisfies
`decode (code x) = x` for every `x ∈ K`. Empty carriers require no chosen default value.
-/

@[expose] public section

namespace Set.Finite

/-- A finite subset has a finite encoding whose decoder recovers every supported value. -/
theorem exists_fin_encoding
    -- `X` is the original alphabet; `K` is the finite subset that must round-trip.
    {X : Type*} {K : Set X} (finite : K.Finite) :
    ∃ (n : ℕ) (code : X → Fin n) (decode : Fin n ↪ X),
      ∀ x ∈ K, decode (code x) = x := by
  classical
  rcases isEmpty_or_nonempty X with empty | nonempty
  · let : IsEmpty X := empty
    exact ⟨0, isEmptyElim, Function.Embedding.ofIsEmpty, fun x _ => isEmptyElim x⟩
  · let x₀ : X := Classical.choice nonempty
    -- One fallback value makes the finite alphabet nonempty even when `K` is empty.
    obtain ⟨n, decode, covers⟩ := (finite.insert x₀).fin_embedding
    have contains : x₀ ∈ Set.range decode := by
      rw [covers]
      exact Set.mem_insert x₀ K
    obtain ⟨i, _⟩ := contains
    let : Nonempty (Fin n) := ⟨i⟩
    refine ⟨n, Function.invFun decode, decode, ?_⟩
    intro x supported
    -- Inverting the finite enumeration recovers every value in its range.
    apply Function.invFun_eq
    change x ∈ Set.range decode
    rw [covers]
    exact Set.mem_insert_of_mem x₀ supported

end Set.Finite
