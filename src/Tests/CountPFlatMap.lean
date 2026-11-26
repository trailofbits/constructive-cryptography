module

public import Probability.List

/-!
# Counting selected outputs of list expansions

Only entries of the selected source list need the per-block bound. Another source entry
has two selected outputs and would violate that bound.
-/

@[expose] public section

namespace Tests.CountPFlatMap

/-- `none` produces an uncounted false; the two other markers produce one or two truths. -/
def replies : Option Bool → List Bool
  | none => [false]
  | some false => [true]
  | some true => [true, true]

example : ([none, some false].flatMap replies).countP id ≤ 1 := by
  apply List.countP_flatMap_le_mul_countP Option.isSome id replies 1
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · change 0 ≤ 0
    exact Nat.le_refl _
  · change 1 ≤ 1
    exact Nat.le_refl _

/-- A marker absent from the source list prevents a global version of the cost hypothesis. -/
example : ¬ (replies (some true)).countP id ≤ 1 := by
  change ¬ 2 ≤ 1
  omega

#print axioms List.countP_flatMap_le_mul_countP

end Tests.CountPFlatMap
