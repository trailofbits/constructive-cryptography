module

public import ConstructiveCryptography.Game

/-!
# Games testing a submitted value

`SubmissionGame` interprets sets of successful submissions as games. Its admitted winners
are monotone in that set and satisfy a two-event union bound. These are explicit contracts
on the selected interpretation; the performance type remains the one chosen by `Games`.

`SubmissionGame.reindex` tests decoded submissions by pulling a set back along the decoder.
A local inclusion `p ⊆ q ∪ r` gives the calculation

```text
W (game p) ≤ W (game (q ∪ r)) ≤ W (game q) + W (game r).
              mono                  union_le
```
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography

universe u v w x z

/-- A submission interpretation `game p` tests membership in `p`; admitted evaluations are
monotone and satisfy `W (game (p ∪ q)) ≤ W (game p) + W (game q)`. -/
structure SubmissionGame
    -- `I` carries interfaces, and `Game A` carries games at the selected `A : I`.
    {I : Type u} (Game : I → Type v)
    -- Ω orders performances from worse to better and adds the two event bounds.
    (Ω : Type z) [Preorder Ω] [Add Ω] [Games I Game Ω]
    -- `X` carries submitted values; `A` is their game interface.
    (X : Type w) (A : I) where
  /-- `game p` is the game testing whether the submitted value lies in `p`. -/
  game : Set X → Game A
  /-- Enlarging `p` cannot decrease an admitted winner's performance on `game p`. -/
  mono : ∀ W ∈ Games.winners A, Monotone (W ∘ game)
  /-- Performance on a union is at most the sum of the two event performances. -/
  union_le : ∀ W ∈ Games.winners A, ∀ p q,
    W (game (p ∪ q)) ≤ W (game p) + W (game q)

namespace SubmissionGame

/-- Test decoded submissions by preimage:
`(S.reindex decode).game p = S.game (decode ⁻¹' p)`. -/
def reindex
    -- `Game A` carries games at interface `A : I`; Ω carries their ordered additive scores.
    {I : Type u} {Game : I → Type v} {Ω : Type z}
    [Preorder Ω] [Add Ω] [Games I Game Ω]
    -- `S` tests actual submissions in `Y`; `X` carries their decoded values.
    {X : Type w} {Y : Type x} {A : I} (S : SubmissionGame Game Ω Y A)
    (decode : Y → X) : SubmissionGame Game Ω X A where
  game p := S.game (decode ⁻¹' p)
  mono W admitted _ _ inclusion := S.mono W admitted (Set.preimage_mono inclusion)
  union_le W admitted p q := S.union_le W admitted (decode ⁻¹' p) (decode ⁻¹' q)

end SubmissionGame

end ConstructiveCryptography
