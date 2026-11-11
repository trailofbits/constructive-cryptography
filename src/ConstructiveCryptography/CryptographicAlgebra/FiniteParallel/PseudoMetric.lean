module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel
public import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Distance bounds for finite parallel families

`distance_parallelAll_le_sum` derives finite subadditivity from binary parallel
non-expansion. Reindexing and head/tail splitting preserve distance through their explicit
isomorphisms; the empty family is the selected dummy resource. Single-component replacement
and scalar error budgets then follow by finite-sum laws. Attaching a common outside converter
uses the existing non-expansion law.
-/

public section

namespace ConstructiveCryptography.FiniteParallel

open CategoryTheory MonoidalCategory CryptographicAlgebra
open scoped BigOperators NNReal ConstructiveCryptography.FiniteParallel

universe u v w

-- `C` carries interfaces and converters; `Phi A` carries resources on interface `A`.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable [CompatiblePseudoMetric C Phi] [FiniteParallel C Phi]

/-- Finite parallel distance is bounded by the sum of component distances, including infinity. -/
theorem distance_parallelAll_le_sum
    -- `K` indexes the component interfaces `A k`; `R k` and `S k` share each interface.
    {K : Type} [Fintype K] {A : K → C} (R S : ∀ k, Phi (A k)) :
    distance (∥ k, R k) (∥ k, S k) ≤ ∑ k, distance (R k) (S k) := by
  refine Fintype.induction_empty_option (P := fun K _ =>
    ∀ (A : K → C) (R S : ∀ k, Phi (A k)),
      distance (∥ k, R k) (∥ k, S k) ≤ ∑ k, distance (R k) (S k)) ?_ ?_ ?_ K A R S
  · intro K L _ e ih A R S
    let : Fintype K := Fintype.ofEquiv L e.symm
    -- Reindex both resources through the same isomorphism, then reindex the sum.
    rw [← reindex_parallelAll e A R, ← reindex_parallelAll e A S]
    change distance (attach _ _) (attach _ _) ≤ _
    rw [distance_attach_iso]
    exact (ih (fun k => A (e k)) (fun k => R (e k)) (fun k => S (e k))).trans_eq
      (Equiv.sum_comp e (fun k => distance (R k) (S k)))
  · intro A R S
    -- Both empty families are the same presentation of the selected dummy.
    rw [← empty_parallelAll A R, ← empty_parallelAll A S, distance_self]
    exact bot_le
  · intro K _ ih A R S
    -- Split into head and tail before applying binary non-expansion and the tail bound.
    rw [← optionSplit_parallelAll A R, ← optionSplit_parallelAll A S]
    change distance (attach _ _) (attach _ _) ≤ _
    rw [distance_attach_iso, Fintype.sum_option]
    exact (distance_parallel_le _ _ _ _).trans
      (add_le_add le_rfl (ih (fun k => A (some k)) (fun k => R (some k))
        (fun k => S (some k))))

/-- Replacing one component costs at most the distance between its two replacements. -/
lemma distance_parallelAll_update_le
    -- `R` supplies unchanged components; `S` and `T` replace the component at `k`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → C}
    (R : ∀ j, Phi (A j)) (k : K) (S T : Phi (A k)) :
    distance (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤
      distance S T := by
  refine (distance_parallelAll_le_sum _ _).trans_eq ?_
  rw [Finset.sum_eq_single k]
  · rw [Function.update_self, Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj, distance_self]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Supplied nonnegative scalar component budgets add without truncation. -/
lemma distance_parallelAll_le_sum_of_le
    -- `R k` and `S k` are resources at `A k`; `error k` is their nonnegative scalar budget.
    {K : Type} [Fintype K] {A : K → C} (R S : ∀ k, Phi (A k)) (error : K → ℝ≥0)
    -- `step k` supplies only the distance bound for that local pair.
    (step : ∀ k, distance (R k) (S k) ≤ (error k : ENNReal)) :
    distance (∥ k, R k) (∥ k, S k) ≤ ((∑ k, error k : ℝ≥0) : ENNReal) := by
  refine (distance_parallelAll_le_sum R S).trans ?_
  rw [ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_le_sum (fun k _ => step k)

/-- A shared outside converter preserves the sum of the supplied component budgets. -/
lemma distance_attach_parallelAll_le_sum
    -- `context` presents outside `X` while using the family interfaces `A` inside.
    {K : Type} [Fintype K] {A : K → C} {X : C}
    (context : X ⟶ (⨂ k, A k)) (R S : ∀ k, Phi (A k)) (error : K → ℝ≥0)
    -- `step k` supplies only the distance bound for that local pair.
    (step : ∀ k, distance (R k) (S k) ≤ (error k : ENNReal)) :
    distance (context • (∥ k, R k)) (context • (∥ k, S k)) ≤
      ((∑ k, error k : ℝ≥0) : ENNReal) :=
  (distance_attach_le context _ _).trans (distance_parallelAll_le_sum_of_le R S error step)

end ConstructiveCryptography.FiniteParallel
