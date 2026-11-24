module

public import Probability.List
public import Mathlib.Tactic.NormNum

/-!
# List splits and fold-indexed predicates

Tests `List.exists_eq_append_cons_iff`, `List.forall_prefix_concat_iff_forall_take`,
`List.exists_split_of_filterMap_eq`, `List.exists_split_of_filter_eq`, and `List.ForallScan`
on concrete lists:

* checking whether some entry of `[1, 2, 4]` exceeds the sum of the entries before it;
* splitting `[1, 2, 3, 4]` at an entry of its even entries (`filterMap` and `filter`);
* checking a predicate against the running sum on a list split in two.
-/

@[expose] public section

namespace Tests.ProbabilityList

/-- Some entry of `[1, 2, 4]` is larger than the sum of the entries before it (`4 > 1 + 2`),
using `List.exists_eq_append_cons_iff`. -/
example : ∃ p e s, ([1, 2, 4] : List ℕ) = p ++ e :: s ∧ p.sum < e := by
  rw [List.exists_eq_append_cons_iff]
  exact ⟨2, by norm_num, by norm_num⟩

/-- No entry of `[0, 0, 0]` is strictly larger than the sum of the entries before it. -/
example : ¬ ∃ p e s, ([0, 0, 0] : List ℕ) = p ++ e :: s ∧ p.sum < e := by
  rw [List.exists_eq_append_cons_iff]
  rintro ⟨i, hi, hlt⟩
  have hzero : ([0, 0, 0] : List ℕ)[i] = 0 := by
    have hm := List.getElem_mem hi
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hm
  rw [hzero] at hlt
  exact Nat.not_lt_zero _ hlt

/-- Every entry of `[1, 1, 2, 4]` is at most `1 + sum` of the entries before it, using
`List.forall_prefix_concat_iff_forall_take`. -/
example : ∀ p e, p ++ [e] <+: ([1, 1, 2, 4] : List ℕ) → e ≤ p.sum + 1 := by
  rw [List.forall_prefix_concat_iff_forall_take]
  intro i hi
  have positions : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases positions with rfl | rfl | rfl | rfl <;> norm_num

/-- Splitting `[1, 2, 3, 4]` at the second even entry `4` (mapped to `2` via `filterMap`) recovers
the preimage split `[1, 2, 3] ++ 4 :: []`. -/
example :
    let evenHalf : ℕ → Option ℕ := fun n => if n % 2 = 0 then some (n / 2) else none
    ∃ l₁ a l₂, ([1, 2, 3, 4] : List ℕ) = l₁ ++ a :: l₂ ∧
      l₁.filterMap evenHalf = [1] ∧ evenHalf a = some 2 ∧ l₂.filterMap evenHalf = [] := by
  intro evenHalf
  exact List.exists_split_of_filterMap_eq evenHalf [1, 2, 3, 4] [1] 2 [] rfl

/-- Splitting `[1, 2, 3, 4]` at the second even entry `4` in the `filter` form recovers the prefix
with `[2]` before `4` and `[]` after. -/
example :
    ∃ l₁ l₂, ([1, 2, 3, 4] : List ℕ) = l₁ ++ 4 :: l₂ ∧
      l₁.filter (fun n => n % 2 == 0) = [2] ∧ (4 % 2 == 0) = true ∧
      l₂.filter (fun n => n % 2 == 0) = [] :=
  List.exists_split_of_filter_eq (fun n => n % 2 == 0) [1, 2, 3, 4] [2] 4 [] rfl

/-- With a running sum as the fold, joining `[1, 2]` (scanned from `0`) and `[3, 6]` (scanned from
`3`) satisfies `c ≤ a` at every entry, and splitting at `6` yields `1 + 2 + 3 ≤ 6`. -/
example :
    List.ForallScan (· + ·) (fun c a => c ≤ a) 0 ([1, 2] ++ [3, 6]) ∧
      ([1, 2, 3] : List ℕ).foldl (· + ·) 0 ≤ 6 := by
  have h1 : List.ForallScan (· + ·) (fun c a => c ≤ a) (0 : ℕ) [1, 2] := by
    norm_num [List.ForallScan, List.foldl_cons, List.foldl_nil]
  have h2 : List.ForallScan (· + ·) (fun c a => c ≤ a) (([1, 2] : List ℕ).foldl (· + ·) 0)
      [3, 6] := by norm_num [List.ForallScan, List.foldl_cons, List.foldl_nil]
  have h12 : List.ForallScan (· + ·) (fun c a => c ≤ a) (0 : ℕ) ([1, 2] ++ [3, 6]) :=
    h1.append h2
  refine ⟨h12, ?_⟩
  exact List.ForallScan.of_append_cons (l := [1, 2, 3]) (a := 6) (m := []) h12

/-- The recursive instance supplies decidability from the entry predicate. -/
example : Decidable (List.ForallScan (· + ·) (fun c a => c ≤ a) (0 : ℕ) [1, 2]) :=
  inferInstance

#print axioms List.exists_eq_append_cons_iff
#print axioms List.forall_prefix_concat_iff_forall_take
#print axioms List.exists_split_of_filterMap_eq
#print axioms List.exists_split_of_filter_eq
#print axioms List.ForallScan.append
#print axioms List.ForallScan.of_append_cons
#print axioms List.forallScan_append_iff
#print axioms List.forallScan_iff_forall_prefix

end Tests.ProbabilityList
