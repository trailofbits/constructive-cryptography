module

public import RandomSystems.Distance.UntilBad

/-!
# Costs of fresh projected inputs

Exact repeats and different queries with the same parity are charged once. Negative charges
remain valid, and the collision-pair formula uses the same projected distinct count.
-/

@[expose] public section

namespace Tests.FreshInputCost

open SystemAlgebra

/-- Repeating input 4 leaves three distinct inputs, each charged `−2`. -/
example : transcriptCost (fun h (x : ℕ) => if x ∈ h.map Prod.fst then 0 else (-2 : ℝ))
    [(4, false), (9, true), (4, true), (11, false)] = -6 := by
  have total := transcriptCost_fresh_eq_card_mul id (-2)
    [(4, false), (9, true), (4, true), (11, false)]
  norm_num [Function.comp_def, List.toFinset_cons, List.toFinset_nil] at total
  exact total

/-- Four distinct queries have only two parities, so the fresh charge 5 is paid twice. -/
example : transcriptCost (fun h (x : ℕ) =>
    if x % 2 ∈ h.map (fun p => p.1 % 2) then 0 else (5 : ℝ))
    [(4, false), (6, true), (9, true), (11, false)] = 10 := by
  have total := transcriptCost_fresh_eq_card_mul (fun x : ℕ => x % 2) 5
    [(4, false), (6, true), (9, true), (11, false)]
  norm_num [Function.comp_def, List.toFinset_cons, List.toFinset_nil] at total
  exact total

/-- With two distinct parities there is one pair, regardless of repeated queries. -/
example : transcriptCost (fun h (x : ℕ) =>
    if x % 2 ∈ h.map (fun p => p.1 % 2) then 0 else
      ((h.map (fun p => p.1 % 2)).toFinset.card : ℝ) / 4)
    [(4, false), (6, true), (9, true), (11, false)] = 1 / 4 := by
  have total := transcriptCost_distinct_eq_choose (fun x : ℕ => x % 2) 4
    [(4, false), (6, true), (9, true), (11, false)]
  norm_num [Function.comp_def, List.toFinset_cons, List.toFinset_nil] at total
  exact total

#print axioms SystemAlgebra.transcriptCost_distinct_eq_sub
#print axioms SystemAlgebra.transcriptCost_fresh_eq_card_mul
#print axioms SystemAlgebra.transcriptCost_distinct_eq_choose

end Tests.FreshInputCost
