module

public import Commons.Definitions.CollisionBound

/-!
# A client of the adaptive collision bound

The generated `Evaluation` interface supplies its original query domain and length bound.
Every admitted game winner then has collision probability at most `C(q, 2) / |Y|` by the
named result, without unfolding the function table or the winner.
-/

@[expose] public section

namespace CollisionBoundTests

open SystemAlgebra Commons
open scoped NNReal

open Classical in
/-- Any admitted winner on the evaluation interface satisfies the birthday bound. -/
lemma evaluation_collision_win_le
    -- `X`, `Y` are finite alphabets, with nonempty replies; `q` bounds all evaluation queries.
    {X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] (q : ℕ)
    -- `hw` supplies the compatible stopping winner; no table or adversary is unfolded.
    {winner : TypedGame (Evaluation X Y q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners (Evaluation X Y q)) :
    winner (URF.collisionGame (Evaluation X Y q)) ≤
      ((q.choose 2 : ℝ≥0) / Fintype.card Y : ℝ≥0) := by
  apply URF.collisionGame_win_le (Evaluation X Y q).domain
    (Evaluation X Y q).nonempty_prefix q (Evaluation X Y q).length_le q _ hw
  -- There are no more distinct tested inputs than queries in an admitted list.
  intro xs hxs
  exact (List.toFinset_card_le _).trans (by simpa only [List.length_map] using hxs.2)

#print axioms evaluation_collision_win_le

end CollisionBoundTests
