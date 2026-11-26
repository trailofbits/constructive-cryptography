module

public import Probability.List

/-!
# Stable first-occurrence positions

Repeated natural-number inputs keep their first position as a query prefix grows. The rank
calculation uses `eraseDups` and `idxOf` directly, including with a chosen lawful comparison.
-/

@[expose] public section

namespace Tests.FirstOccurrences

/-- Repetitions of `7` and `9` leave the chronological first occurrences `[7,9,11]`. -/
example : ([7, 9, 7, 11, 9] : List ℕ).eraseDups = [7, 9, 11] := rfl

/-- Keeping first occurrences preserves the actual query prefix despite later repetitions. -/
example [BEq ℕ] [LawfulBEq ℕ] :
    ([7, 9, 7] : List ℕ).eraseDups <+: [7, 9, 7, 11, 9].eraseDups :=
  (show ([7, 9, 7] : List ℕ) <+: [7, 9, 7, 11, 9] from ⟨[11, 9], rfl⟩).eraseDups

/-- The old input `9` keeps its rank under the same selected equality comparison. -/
example [BEq ℕ] [LawfulBEq ℕ] :
    ([7, 9, 7] : List ℕ).eraseDups.idxOf 9 = [7, 9, 7, 11, 9].eraseDups.idxOf 9 := by
  have initial : ([7, 9, 7] : List ℕ) <+: [7, 9, 7, 11, 9] := ⟨[11, 9], rfl⟩
  apply initial.eraseDups.idxOf_eq_of_mem
  exact List.mem_eraseDups.mpr (List.mem_cons_of_mem 7 List.mem_cons_self)

/-- The distinct-input list is duplicate-free even when the original alphabet is infinite. -/
example [BEq ℕ] [LawfulBEq ℕ] : ([7, 9, 7, 11, 9] : List ℕ).eraseDups.Nodup :=
  List.nodup_eraseDups _

/-- In a two-label pool the third fresh input has rank `2`; a later repeat still has rank `1`. -/
example :
    ([7, 9, 7, 11] : List ℕ).eraseDups.idxOf 11 = 2 ∧
      ([7, 9, 7, 11, 9] : List ℕ).eraseDups.idxOf 9 = 1 := ⟨rfl, rfl⟩

#print axioms List.IsPrefix.eraseDups
#print axioms List.nodup_eraseDups

end Tests.FirstOccurrences
