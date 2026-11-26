module

public import RandomSystems.Cumulative.CumulativeObservation

/-!
# Fixed-query observations

The query list `[7, 9]` has bound two. Its observed query prefix is `[7]` at horizon one
and `[7, 9]` after completion. An empty query list stays empty at every tested horizon.
Queries use ℕ, so the contracts require no finite query alphabet.
-/

@[expose] public section

namespace Tests.FixedQueries

open SystemAlgebra

/-- The two exchanges follow `[7, 9]`, with unit replies. -/
lemma follows_two :
    FollowsStrategy (fixedQueries [7, 9]) ([(7, ()), (9, ())] : List (ℕ × Unit)) := by
  apply FollowsStrategy.iff_getElem.mpr
  intro i hi
  have index : i = 0 ∨ i = 1 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases index with rfl | rfl <;> exact Part.mem_some _

/-- An empty fixed query list permits no query. -/
example : QueryBounded 0 (DDE.ofQueries (X := ℕ) (Y := Unit) []) :=
  DDE.ofQueries_queryBounded []

/-- Two listed queries give a bound of two even with an infinite query alphabet. -/
example : QueryBounded 2 (DDE.ofQueries (Y := Unit) [7, 9]) :=
  DDE.ofQueries_queryBounded [7, 9]

/-- The empty query list is complete before horizon three. -/
example : ([] : List (ℕ × Unit)).map Prod.fst = ([] : List ℕ).take 3 := by
  have good : Good (fixedQueries ([] : List ℕ)) 3 ([] : List (ℕ × Unit)) :=
    ⟨FollowsStrategy.nil, Or.inr ⟨by norm_num, fun impossible => impossible⟩⟩
  exact good.fixedQueries

/-- At horizon one, only the first of the two queries has been observed. -/
example : ([(7, ())] : List (ℕ × Unit)).map Prod.fst = [7, 9].take 1 := by
  have follows := follows_two.of_prefix (show [(7, ())] <+: [(7, ()), (9, ())] from
    ⟨[(9, ())], rfl⟩)
  have good : Good (fixedQueries [7, 9]) 1 ([(7, ())] : List (ℕ × Unit)) :=
    ⟨follows, Or.inl rfl⟩
  exact good.fixedQueries

/-- Beyond horizon two, the completed observation still contains both queries. -/
example : ([(7, ()), (9, ())] : List (ℕ × Unit)).map Prod.fst = [7, 9].take 5 := by
  have good : Good (fixedQueries [7, 9]) 5 ([(7, ()), (9, ())] : List (ℕ × Unit)) :=
    ⟨follows_two, Or.inr ⟨by norm_num, fun impossible => impossible⟩⟩
  exact good.fixedQueries

#print axioms SystemAlgebra.DDE.ofQueries_queryBounded
#print axioms SystemAlgebra.Good.fixedQueries

end Tests.FixedQueries
