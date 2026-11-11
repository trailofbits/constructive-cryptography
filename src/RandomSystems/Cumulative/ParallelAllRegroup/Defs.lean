module

public import RandomSystems.Cumulative.ParallelAll

/-!
# Splitting finite-family alphabets

`optionSplit` presents the alphabet of an `Option J` family as the head alphabet beside the
`J`-indexed tail. It preserves every local input and reply; it changes only their tags.
-/

@[expose] public section

namespace SystemAlgebra

open Classical in
/-- An `Option J`-tagged alphabet as a pair: the alphabet at `none`, and the `J`-tagged alphabet
at `some j`, `⟨some j, a⟩ ↦ ⟨some (), ⟨j, a⟩⟩`. -/
def optionSplit {J : Type} (A : Option J → Type) :
    (Σ k, A k) ≃ Two (A none) (Σ j, A (some j)) where
  toFun
    | ⟨none, a⟩ => ⟨none, a⟩
    | ⟨some j, a⟩ => ⟨some (), ⟨j, a⟩⟩
  invFun
    | ⟨none, a⟩ => ⟨none, a⟩
    | ⟨some (), ⟨j, a⟩⟩ => ⟨some j, a⟩
  left_inv := by rintro ⟨(_ | j), a⟩ <;> rfl
  right_inv := by rintro ⟨(_ | ⟨⟨⟩⟩), a⟩ <;> rfl

end SystemAlgebra
