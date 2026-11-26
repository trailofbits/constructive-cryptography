module

public import RandomSystems.Distance.UntilBad

/-!
# A signed transcript potential

The potential `7 − 2 · length(h)` starts at 7 and decreases by 2 per exchange. Its cost is
zero on the empty history and −6 after three exchanges. Queries use the infinite carrier ℕ.
-/

@[expose] public section

namespace Tests.TranscriptCost

open SystemAlgebra

/-- The fixed potential is `Φ(h) = 7 − 2 · length(h)`. -/
def potential (h : List (ℕ × Unit)) : ℝ := 7 - 2 * h.length

/-- Each exchange decreases this potential by two. -/
lemma potential_snoc (h : List (ℕ × Unit)) (x : ℕ) (y : Unit) :
    potential (h ++ [(x, y)]) = potential h + (-2) := by
  simp only [potential, List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  ring

/-- The initial value cancels before any exchange. -/
example : transcriptCost (fun _ _ => (-2 : ℝ)) ([] : List (ℕ × Unit)) = 0 := by
  simpa only [sub_self] using
    transcriptCost_eq_sub_of_snoc (fun _ _ => (-2 : ℝ)) potential potential_snoc []

/-- Three exchanges cost `−6`; repeating a query still incurs this constant charge. -/
example : transcriptCost (fun _ _ => (-2 : ℝ)) [(4, ()), (9, ()), (4, ())] = -6 := by
  have total := transcriptCost_eq_sub_of_snoc (fun _ _ => (-2 : ℝ)) potential
    potential_snoc [(4, ()), (9, ()), (4, ())]
  norm_num [potential] at total ⊢
  exact total

#print axioms SystemAlgebra.transcriptCost_eq_sub_of_snoc

end Tests.TranscriptCost
